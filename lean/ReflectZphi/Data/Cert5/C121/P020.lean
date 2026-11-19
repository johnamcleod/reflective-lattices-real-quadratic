import ReflectZphi.Data.Cert5.C121.Base

namespace ReflectZphi.Data.Cert5.C121

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd7_2_896 : subd7_2 [1, 3, -8] = true := by decide +kernel
theorem subd7_2_897 : subd7_2 [1, 3, -7] = true := by decide +kernel
theorem subd7_2_898 : subd7_2 [1, 3, -6] = true := by decide +kernel
theorem subd7_2_899 : subd7_2 [1, 3, -5] = true := by decide +kernel
theorem subd7_2_900 : subd7_2 [1, 3, -4] = true := by decide +kernel
theorem subd7_2_901 : subd7_2 [1, 3, -3] = true := by decide +kernel
theorem subd7_2_902 : subd7_2 [1, 3, -2] = true := by decide +kernel
theorem subd7_2_903 : subd7_2 [1, 3, -1] = true := by decide +kernel
theorem subd7_2_904 : subd7_2 [1, 3, 0] = true := by decide +kernel
theorem subd7_2_905 : subd7_2 [1, 3, 1] = true := by decide +kernel
theorem subd7_2_906 : subd7_2 [1, 3, 2] = true := by decide +kernel
theorem subd7_2_907 : subd7_2 [1, 3, 3] = true := by decide +kernel
theorem subd7_2_908 : subd7_2 [1, 3, 4] = true := by decide +kernel
theorem subd7_2_909 : subd7_2 [1, 3, 5] = true := by decide +kernel
theorem subd7_2_910 : subd7_2 [1, 3, 6] = true := by decide +kernel
theorem subd7_2_911 : subd7_2 [1, 4, -10] = true := by decide +kernel
theorem subd7_2_912 : subd7_2 [1, 4, -9] = true := by decide +kernel
theorem subd7_2_913 : subd7_2 [1, 4, -8] = true := by decide +kernel
theorem subd7_2_914 : subd7_2 [1, 4, -7] = true := by decide +kernel
theorem subd7_2_915 : subd7_2 [1, 4, -6] = true := by decide +kernel
theorem subd7_2_916 : subd7_2 [1, 4, -5] = true := by decide +kernel
theorem subd7_2_917 : subd7_2 [1, 4, -4] = true := by decide +kernel
theorem subd7_2_918 : subd7_2 [1, 4, -3] = true := by decide +kernel
theorem subd7_2_919 : subd7_2 [1, 4, -2] = true := by decide +kernel
theorem subd7_2_920 : subd7_2 [1, 4, -1] = true := by decide +kernel
theorem subd7_2_921 : subd7_2 [1, 4, 0] = true := by decide +kernel
theorem subd7_2_922 : subd7_2 [1, 4, 1] = true := by decide +kernel
theorem subd7_2_923 : subd7_2 [1, 4, 2] = true := by decide +kernel
theorem subd7_2_924 : subd7_2 [1, 4, 3] = true := by decide +kernel
theorem subd7_2_925 : subd7_2 [1, 4, 4] = true := by decide +kernel
theorem subd7_2_926 : subd7_2 [1, 4, 5] = true := by decide +kernel
theorem subd7_2_927 : subd7_2 [1, 5] = true := by decide +kernel
theorem sbd7_2_28 : ∀ q ∈ blkd7_2_28, subd7_2 q = true := by
  unfold blkd7_2_28
  exact List.forall_mem_cons.2 ⟨subd7_2_896, List.forall_mem_cons.2 ⟨subd7_2_897, List.forall_mem_cons.2 ⟨subd7_2_898, List.forall_mem_cons.2 ⟨subd7_2_899, List.forall_mem_cons.2 ⟨subd7_2_900, List.forall_mem_cons.2 ⟨subd7_2_901, List.forall_mem_cons.2 ⟨subd7_2_902, List.forall_mem_cons.2 ⟨subd7_2_903, List.forall_mem_cons.2 ⟨subd7_2_904, List.forall_mem_cons.2 ⟨subd7_2_905, List.forall_mem_cons.2 ⟨subd7_2_906, List.forall_mem_cons.2 ⟨subd7_2_907, List.forall_mem_cons.2 ⟨subd7_2_908, List.forall_mem_cons.2 ⟨subd7_2_909, List.forall_mem_cons.2 ⟨subd7_2_910, List.forall_mem_cons.2 ⟨subd7_2_911, List.forall_mem_cons.2 ⟨subd7_2_912, List.forall_mem_cons.2 ⟨subd7_2_913, List.forall_mem_cons.2 ⟨subd7_2_914, List.forall_mem_cons.2 ⟨subd7_2_915, List.forall_mem_cons.2 ⟨subd7_2_916, List.forall_mem_cons.2 ⟨subd7_2_917, List.forall_mem_cons.2 ⟨subd7_2_918, List.forall_mem_cons.2 ⟨subd7_2_919, List.forall_mem_cons.2 ⟨subd7_2_920, List.forall_mem_cons.2 ⟨subd7_2_921, List.forall_mem_cons.2 ⟨subd7_2_922, List.forall_mem_cons.2 ⟨subd7_2_923, List.forall_mem_cons.2 ⟨subd7_2_924, List.forall_mem_cons.2 ⟨subd7_2_925, List.forall_mem_cons.2 ⟨subd7_2_926, List.forall_mem_cons.2 ⟨subd7_2_927, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_928 : subd7_2 [2, -7] = true := by decide +kernel
theorem subd7_2_929 : subd7_2 [2, -6] = true := by decide +kernel
theorem subd7_2_930 : subd7_2 [2, -5, -5] = true := by decide +kernel
theorem subd7_2_931 : subd7_2 [2, -5, -4] = true := by decide +kernel
theorem subd7_2_932 : subd7_2 [2, -5, -3] = true := by decide +kernel
theorem subd7_2_933 : subd7_2 [2, -5, -2] = true := by decide +kernel
theorem subd7_2_934 : subd7_2 [2, -5, -1] = true := by decide +kernel
theorem subd7_2_935 : subd7_2 [2, -5, 0] = true := by decide +kernel
theorem subd7_2_936 : subd7_2 [2, -5, 1] = true := by decide +kernel
theorem subd7_2_937 : subd7_2 [2, -5, 2] = true := by decide +kernel
theorem subd7_2_938 : subd7_2 [2, -5, 3] = true := by decide +kernel
theorem subd7_2_939 : subd7_2 [2, -5, 4] = true := by decide +kernel
theorem subd7_2_940 : subd7_2 [2, -5, 5] = true := by decide +kernel
theorem subd7_2_941 : subd7_2 [2, -5, 6] = true := by decide +kernel
theorem subd7_2_942 : subd7_2 [2, -5, 7] = true := by decide +kernel
theorem subd7_2_943 : subd7_2 [2, -5, 8] = true := by decide +kernel
theorem subd7_2_944 : subd7_2 [2, -4, -7] = true := by decide +kernel
theorem subd7_2_945 : subd7_2 [2, -4, -6] = true := by decide +kernel
theorem subd7_2_946 : subd7_2 [2, -4, -5] = true := by decide +kernel
theorem subd7_2_947 : subd7_2 [2, -4, -4] = true := by decide +kernel
theorem subd7_2_948 : subd7_2 [2, -4, -3] = true := by decide +kernel
theorem subd7_2_949 : subd7_2 [2, -4, -2] = true := by decide +kernel
theorem subd7_2_950 : subd7_2 [2, -4, -1] = true := by decide +kernel
theorem subd7_2_951 : subd7_2 [2, -4, 0] = true := by decide +kernel
theorem subd7_2_952 : subd7_2 [2, -4, 1] = true := by decide +kernel
theorem subd7_2_953 : subd7_2 [2, -4, 2] = true := by decide +kernel
theorem subd7_2_954 : subd7_2 [2, -4, 3] = true := by decide +kernel
theorem subd7_2_955 : subd7_2 [2, -4, 4] = true := by decide +kernel
theorem subd7_2_956 : subd7_2 [2, -4, 5] = true := by decide +kernel
theorem subd7_2_957 : subd7_2 [2, -4, 6] = true := by decide +kernel
theorem subd7_2_958 : subd7_2 [2, -4, 7] = true := by decide +kernel
theorem subd7_2_959 : subd7_2 [2, -4, 8] = true := by decide +kernel
theorem sbd7_2_29 : ∀ q ∈ blkd7_2_29, subd7_2 q = true := by
  unfold blkd7_2_29
  exact List.forall_mem_cons.2 ⟨subd7_2_928, List.forall_mem_cons.2 ⟨subd7_2_929, List.forall_mem_cons.2 ⟨subd7_2_930, List.forall_mem_cons.2 ⟨subd7_2_931, List.forall_mem_cons.2 ⟨subd7_2_932, List.forall_mem_cons.2 ⟨subd7_2_933, List.forall_mem_cons.2 ⟨subd7_2_934, List.forall_mem_cons.2 ⟨subd7_2_935, List.forall_mem_cons.2 ⟨subd7_2_936, List.forall_mem_cons.2 ⟨subd7_2_937, List.forall_mem_cons.2 ⟨subd7_2_938, List.forall_mem_cons.2 ⟨subd7_2_939, List.forall_mem_cons.2 ⟨subd7_2_940, List.forall_mem_cons.2 ⟨subd7_2_941, List.forall_mem_cons.2 ⟨subd7_2_942, List.forall_mem_cons.2 ⟨subd7_2_943, List.forall_mem_cons.2 ⟨subd7_2_944, List.forall_mem_cons.2 ⟨subd7_2_945, List.forall_mem_cons.2 ⟨subd7_2_946, List.forall_mem_cons.2 ⟨subd7_2_947, List.forall_mem_cons.2 ⟨subd7_2_948, List.forall_mem_cons.2 ⟨subd7_2_949, List.forall_mem_cons.2 ⟨subd7_2_950, List.forall_mem_cons.2 ⟨subd7_2_951, List.forall_mem_cons.2 ⟨subd7_2_952, List.forall_mem_cons.2 ⟨subd7_2_953, List.forall_mem_cons.2 ⟨subd7_2_954, List.forall_mem_cons.2 ⟨subd7_2_955, List.forall_mem_cons.2 ⟨subd7_2_956, List.forall_mem_cons.2 ⟨subd7_2_957, List.forall_mem_cons.2 ⟨subd7_2_958, List.forall_mem_cons.2 ⟨subd7_2_959, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_960 : subd7_2 [2, -4, 9] = true := by decide +kernel
theorem subd7_2_961 : subd7_2 [2, -3, -9] = true := by decide +kernel
theorem subd7_2_962 : subd7_2 [2, -3, -8] = true := by decide +kernel
theorem subd7_2_963 : subd7_2 [2, -3, -7] = true := by decide +kernel
theorem subd7_2_964 : subd7_2 [2, -3, -6] = true := by decide +kernel
theorem subd7_2_965 : subd7_2 [2, -3, -5] = true := by decide +kernel
theorem subd7_2_966 : subd7_2 [2, -3, -4] = true := by decide +kernel
theorem subd7_2_967 : subd7_2 [2, -3, -3] = true := by decide +kernel
theorem subd7_2_968 : subd7_2 [2, -3, -2] = true := by decide +kernel
theorem subd7_2_969 : subd7_2 [2, -3, -1] = true := by decide +kernel
theorem subd7_2_970 : subd7_2 [2, -3, 0] = true := by decide +kernel
theorem subd7_2_971 : subd7_2 [2, -3, 1] = true := by decide +kernel
theorem subd7_2_972 : subd7_2 [2, -3, 2] = true := by decide +kernel
theorem subd7_2_973 : subd7_2 [2, -3, 3] = true := by decide +kernel
theorem subd7_2_974 : subd7_2 [2, -3, 4] = true := by decide +kernel
theorem subd7_2_975 : subd7_2 [2, -3, 5] = true := by decide +kernel
theorem subd7_2_976 : subd7_2 [2, -3, 6] = true := by decide +kernel
theorem subd7_2_977 : subd7_2 [2, -3, 7] = true := by decide +kernel
theorem subd7_2_978 : subd7_2 [2, -3, 8] = true := by decide +kernel
theorem subd7_2_979 : subd7_2 [2, -3, 9] = true := by decide +kernel
theorem subd7_2_980 : subd7_2 [2, -2, -9] = true := by decide +kernel
theorem subd7_2_981 : subd7_2 [2, -2, -8] = true := by decide +kernel
theorem subd7_2_982 : subd7_2 [2, -2, -7] = true := by decide +kernel
theorem subd7_2_983 : subd7_2 [2, -2, -6] = true := by decide +kernel
theorem subd7_2_984 : subd7_2 [2, -2, -5] = true := by decide +kernel
theorem subd7_2_985 : subd7_2 [2, -2, -4] = true := by decide +kernel
theorem subd7_2_986 : subd7_2 [2, -2, -3] = true := by decide +kernel
theorem subd7_2_987 : subd7_2 [2, -2, -2] = true := by decide +kernel
theorem subd7_2_988 : subd7_2 [2, -2, -1] = true := by decide +kernel
theorem subd7_2_989 : subd7_2 [2, -2, 0] = true := by decide +kernel
theorem subd7_2_990 : subd7_2 [2, -2, 1] = true := by decide +kernel
theorem subd7_2_991 : subd7_2 [2, -2, 2] = true := by decide +kernel
theorem sbd7_2_30 : ∀ q ∈ blkd7_2_30, subd7_2 q = true := by
  unfold blkd7_2_30
  exact List.forall_mem_cons.2 ⟨subd7_2_960, List.forall_mem_cons.2 ⟨subd7_2_961, List.forall_mem_cons.2 ⟨subd7_2_962, List.forall_mem_cons.2 ⟨subd7_2_963, List.forall_mem_cons.2 ⟨subd7_2_964, List.forall_mem_cons.2 ⟨subd7_2_965, List.forall_mem_cons.2 ⟨subd7_2_966, List.forall_mem_cons.2 ⟨subd7_2_967, List.forall_mem_cons.2 ⟨subd7_2_968, List.forall_mem_cons.2 ⟨subd7_2_969, List.forall_mem_cons.2 ⟨subd7_2_970, List.forall_mem_cons.2 ⟨subd7_2_971, List.forall_mem_cons.2 ⟨subd7_2_972, List.forall_mem_cons.2 ⟨subd7_2_973, List.forall_mem_cons.2 ⟨subd7_2_974, List.forall_mem_cons.2 ⟨subd7_2_975, List.forall_mem_cons.2 ⟨subd7_2_976, List.forall_mem_cons.2 ⟨subd7_2_977, List.forall_mem_cons.2 ⟨subd7_2_978, List.forall_mem_cons.2 ⟨subd7_2_979, List.forall_mem_cons.2 ⟨subd7_2_980, List.forall_mem_cons.2 ⟨subd7_2_981, List.forall_mem_cons.2 ⟨subd7_2_982, List.forall_mem_cons.2 ⟨subd7_2_983, List.forall_mem_cons.2 ⟨subd7_2_984, List.forall_mem_cons.2 ⟨subd7_2_985, List.forall_mem_cons.2 ⟨subd7_2_986, List.forall_mem_cons.2 ⟨subd7_2_987, List.forall_mem_cons.2 ⟨subd7_2_988, List.forall_mem_cons.2 ⟨subd7_2_989, List.forall_mem_cons.2 ⟨subd7_2_990, List.forall_mem_cons.2 ⟨subd7_2_991, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_992 : subd7_2 [2, -2, 3] = true := by decide +kernel
theorem subd7_2_993 : subd7_2 [2, -2, 4] = true := by decide +kernel
theorem subd7_2_994 : subd7_2 [2, -2, 5] = true := by decide +kernel
theorem subd7_2_995 : subd7_2 [2, -2, 6] = true := by decide +kernel
theorem subd7_2_996 : subd7_2 [2, -2, 7] = true := by decide +kernel
theorem subd7_2_997 : subd7_2 [2, -2, 8] = true := by decide +kernel
theorem subd7_2_998 : subd7_2 [2, -2, 9] = true := by decide +kernel
theorem subd7_2_999 : subd7_2 [2, -1, -10] = true := by decide +kernel
theorem subd7_2_1000 : subd7_2 [2, -1, -9] = true := by decide +kernel
theorem subd7_2_1001 : subd7_2 [2, -1, -8] = true := by decide +kernel
theorem subd7_2_1002 : subd7_2 [2, -1, -7] = true := by decide +kernel
theorem subd7_2_1003 : subd7_2 [2, -1, -6] = true := by decide +kernel
theorem subd7_2_1004 : subd7_2 [2, -1, -5] = true := by decide +kernel
theorem subd7_2_1005 : subd7_2 [2, -1, -4] = true := by decide +kernel
theorem subd7_2_1006 : subd7_2 [2, -1, -3] = true := by decide +kernel
theorem subd7_2_1007 : subd7_2 [2, -1, -2] = true := by decide +kernel
theorem subd7_2_1008 : subd7_2 [2, -1, -1] = true := by decide +kernel
theorem subd7_2_1009 : subd7_2 [2, -1, 0] = true := by decide +kernel
theorem subd7_2_1010 : subd7_2 [2, -1, 1] = true := by decide +kernel
theorem subd7_2_1011 : subd7_2 [2, -1, 2] = true := by decide +kernel
theorem subd7_2_1012 : subd7_2 [2, -1, 3] = true := by decide +kernel
theorem subd7_2_1013 : subd7_2 [2, -1, 4] = true := by decide +kernel
theorem subd7_2_1014 : subd7_2 [2, -1, 5] = true := by decide +kernel
theorem subd7_2_1015 : subd7_2 [2, -1, 6] = true := by decide +kernel
theorem subd7_2_1016 : subd7_2 [2, -1, 7] = true := by decide +kernel
theorem subd7_2_1017 : subd7_2 [2, -1, 8] = true := by decide +kernel
theorem subd7_2_1018 : subd7_2 [2, -1, 9] = true := by decide +kernel
theorem subd7_2_1019 : subd7_2 [2, 0, -11] = true := by decide +kernel
theorem subd7_2_1020 : subd7_2 [2, 0, -10] = true := by decide +kernel
theorem subd7_2_1021 : subd7_2 [2, 0, -9] = true := by decide +kernel
theorem subd7_2_1022 : subd7_2 [2, 0, -8] = true := by decide +kernel
theorem subd7_2_1023 : subd7_2 [2, 0, -7] = true := by decide +kernel
theorem sbd7_2_31 : ∀ q ∈ blkd7_2_31, subd7_2 q = true := by
  unfold blkd7_2_31
  exact List.forall_mem_cons.2 ⟨subd7_2_992, List.forall_mem_cons.2 ⟨subd7_2_993, List.forall_mem_cons.2 ⟨subd7_2_994, List.forall_mem_cons.2 ⟨subd7_2_995, List.forall_mem_cons.2 ⟨subd7_2_996, List.forall_mem_cons.2 ⟨subd7_2_997, List.forall_mem_cons.2 ⟨subd7_2_998, List.forall_mem_cons.2 ⟨subd7_2_999, List.forall_mem_cons.2 ⟨subd7_2_1000, List.forall_mem_cons.2 ⟨subd7_2_1001, List.forall_mem_cons.2 ⟨subd7_2_1002, List.forall_mem_cons.2 ⟨subd7_2_1003, List.forall_mem_cons.2 ⟨subd7_2_1004, List.forall_mem_cons.2 ⟨subd7_2_1005, List.forall_mem_cons.2 ⟨subd7_2_1006, List.forall_mem_cons.2 ⟨subd7_2_1007, List.forall_mem_cons.2 ⟨subd7_2_1008, List.forall_mem_cons.2 ⟨subd7_2_1009, List.forall_mem_cons.2 ⟨subd7_2_1010, List.forall_mem_cons.2 ⟨subd7_2_1011, List.forall_mem_cons.2 ⟨subd7_2_1012, List.forall_mem_cons.2 ⟨subd7_2_1013, List.forall_mem_cons.2 ⟨subd7_2_1014, List.forall_mem_cons.2 ⟨subd7_2_1015, List.forall_mem_cons.2 ⟨subd7_2_1016, List.forall_mem_cons.2 ⟨subd7_2_1017, List.forall_mem_cons.2 ⟨subd7_2_1018, List.forall_mem_cons.2 ⟨subd7_2_1019, List.forall_mem_cons.2 ⟨subd7_2_1020, List.forall_mem_cons.2 ⟨subd7_2_1021, List.forall_mem_cons.2 ⟨subd7_2_1022, List.forall_mem_cons.2 ⟨subd7_2_1023, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_1024 : subd7_2 [2, 0, -6] = true := by decide +kernel
theorem subd7_2_1025 : subd7_2 [2, 0, -5] = true := by decide +kernel
theorem subd7_2_1026 : subd7_2 [2, 0, -4] = true := by decide +kernel
theorem subd7_2_1027 : subd7_2 [2, 0, -3] = true := by decide +kernel
theorem subd7_2_1028 : subd7_2 [2, 0, -2] = true := by decide +kernel
theorem subd7_2_1029 : subd7_2 [2, 0, -1] = true := by decide +kernel
theorem subd7_2_1030 : subd7_2 [2, 0, 0] = true := by decide +kernel
theorem subd7_2_1031 : subd7_2 [2, 0, 1] = true := by decide +kernel
theorem subd7_2_1032 : subd7_2 [2, 0, 2] = true := by decide +kernel
theorem subd7_2_1033 : subd7_2 [2, 0, 3] = true := by decide +kernel
theorem subd7_2_1034 : subd7_2 [2, 0, 4] = true := by decide +kernel
theorem subd7_2_1035 : subd7_2 [2, 0, 5] = true := by decide +kernel
theorem subd7_2_1036 : subd7_2 [2, 0, 6] = true := by decide +kernel
theorem subd7_2_1037 : subd7_2 [2, 0, 7] = true := by decide +kernel
theorem subd7_2_1038 : subd7_2 [2, 0, 8] = true := by decide +kernel
theorem subd7_2_1039 : subd7_2 [2, 0, 9] = true := by decide +kernel
theorem subd7_2_1040 : subd7_2 [2, 1, -11] = true := by decide +kernel
theorem subd7_2_1041 : subd7_2 [2, 1, -10] = true := by decide +kernel
theorem subd7_2_1042 : subd7_2 [2, 1, -9] = true := by decide +kernel
theorem subd7_2_1043 : subd7_2 [2, 1, -8] = true := by decide +kernel
theorem subd7_2_1044 : subd7_2 [2, 1, -7] = true := by decide +kernel
theorem subd7_2_1045 : subd7_2 [2, 1, -6] = true := by decide +kernel
theorem subd7_2_1046 : subd7_2 [2, 1, -5] = true := by decide +kernel
theorem subd7_2_1047 : subd7_2 [2, 1, -4] = true := by decide +kernel
theorem subd7_2_1048 : subd7_2 [2, 1, -3] = true := by decide +kernel
theorem subd7_2_1049 : subd7_2 [2, 1, -2] = true := by decide +kernel
theorem subd7_2_1050 : subd7_2 [2, 1, -1] = true := by decide +kernel
theorem subd7_2_1051 : subd7_2 [2, 1, 0] = true := by decide +kernel
theorem subd7_2_1052 : subd7_2 [2, 1, 1] = true := by decide +kernel
theorem subd7_2_1053 : subd7_2 [2, 1, 2] = true := by decide +kernel
theorem subd7_2_1054 : subd7_2 [2, 1, 3] = true := by decide +kernel
theorem subd7_2_1055 : subd7_2 [2, 1, 4] = true := by decide +kernel
theorem sbd7_2_32 : ∀ q ∈ blkd7_2_32, subd7_2 q = true := by
  unfold blkd7_2_32
  exact List.forall_mem_cons.2 ⟨subd7_2_1024, List.forall_mem_cons.2 ⟨subd7_2_1025, List.forall_mem_cons.2 ⟨subd7_2_1026, List.forall_mem_cons.2 ⟨subd7_2_1027, List.forall_mem_cons.2 ⟨subd7_2_1028, List.forall_mem_cons.2 ⟨subd7_2_1029, List.forall_mem_cons.2 ⟨subd7_2_1030, List.forall_mem_cons.2 ⟨subd7_2_1031, List.forall_mem_cons.2 ⟨subd7_2_1032, List.forall_mem_cons.2 ⟨subd7_2_1033, List.forall_mem_cons.2 ⟨subd7_2_1034, List.forall_mem_cons.2 ⟨subd7_2_1035, List.forall_mem_cons.2 ⟨subd7_2_1036, List.forall_mem_cons.2 ⟨subd7_2_1037, List.forall_mem_cons.2 ⟨subd7_2_1038, List.forall_mem_cons.2 ⟨subd7_2_1039, List.forall_mem_cons.2 ⟨subd7_2_1040, List.forall_mem_cons.2 ⟨subd7_2_1041, List.forall_mem_cons.2 ⟨subd7_2_1042, List.forall_mem_cons.2 ⟨subd7_2_1043, List.forall_mem_cons.2 ⟨subd7_2_1044, List.forall_mem_cons.2 ⟨subd7_2_1045, List.forall_mem_cons.2 ⟨subd7_2_1046, List.forall_mem_cons.2 ⟨subd7_2_1047, List.forall_mem_cons.2 ⟨subd7_2_1048, List.forall_mem_cons.2 ⟨subd7_2_1049, List.forall_mem_cons.2 ⟨subd7_2_1050, List.forall_mem_cons.2 ⟨subd7_2_1051, List.forall_mem_cons.2 ⟨subd7_2_1052, List.forall_mem_cons.2 ⟨subd7_2_1053, List.forall_mem_cons.2 ⟨subd7_2_1054, List.forall_mem_cons.2 ⟨subd7_2_1055, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_1056 : subd7_2 [2, 1, 5] = true := by decide +kernel
theorem subd7_2_1057 : subd7_2 [2, 1, 6] = true := by decide +kernel
theorem subd7_2_1058 : subd7_2 [2, 1, 7] = true := by decide +kernel
theorem subd7_2_1059 : subd7_2 [2, 1, 8] = true := by decide +kernel
theorem subd7_2_1060 : subd7_2 [2, 2, -10] = true := by decide +kernel
theorem subd7_2_1061 : subd7_2 [2, 2, -9] = true := by decide +kernel
theorem subd7_2_1062 : subd7_2 [2, 2, -8] = true := by decide +kernel
theorem subd7_2_1063 : subd7_2 [2, 2, -7] = true := by decide +kernel
theorem subd7_2_1064 : subd7_2 [2, 2, -6] = true := by decide +kernel
theorem subd7_2_1065 : subd7_2 [2, 2, -5] = true := by decide +kernel
theorem subd7_2_1066 : subd7_2 [2, 2, -4] = true := by decide +kernel
theorem subd7_2_1067 : subd7_2 [2, 2, -3] = true := by decide +kernel
theorem subd7_2_1068 : subd7_2 [2, 2, -2] = true := by decide +kernel
theorem subd7_2_1069 : subd7_2 [2, 2, -1] = true := by decide +kernel
theorem subd7_2_1070 : subd7_2 [2, 2, 0] = true := by decide +kernel
theorem subd7_2_1071 : subd7_2 [2, 2, 1] = true := by decide +kernel
theorem subd7_2_1072 : subd7_2 [2, 2, 2] = true := by decide +kernel
theorem subd7_2_1073 : subd7_2 [2, 2, 3] = true := by decide +kernel
theorem subd7_2_1074 : subd7_2 [2, 2, 4] = true := by decide +kernel
theorem subd7_2_1075 : subd7_2 [2, 2, 5] = true := by decide +kernel
theorem subd7_2_1076 : subd7_2 [2, 2, 6] = true := by decide +kernel
theorem subd7_2_1077 : subd7_2 [2, 2, 7] = true := by decide +kernel
theorem subd7_2_1078 : subd7_2 [2, 3, -10] = true := by decide +kernel
theorem subd7_2_1079 : subd7_2 [2, 3, -9] = true := by decide +kernel
theorem subd7_2_1080 : subd7_2 [2, 3, -8] = true := by decide +kernel
theorem subd7_2_1081 : subd7_2 [2, 3, -7] = true := by decide +kernel
theorem subd7_2_1082 : subd7_2 [2, 3, -6] = true := by decide +kernel
theorem subd7_2_1083 : subd7_2 [2, 3, -5] = true := by decide +kernel
theorem subd7_2_1084 : subd7_2 [2, 3, -4] = true := by decide +kernel
theorem subd7_2_1085 : subd7_2 [2, 3, -3] = true := by decide +kernel
theorem subd7_2_1086 : subd7_2 [2, 3, -2] = true := by decide +kernel
theorem subd7_2_1087 : subd7_2 [2, 3, -1] = true := by decide +kernel
theorem sbd7_2_33 : ∀ q ∈ blkd7_2_33, subd7_2 q = true := by
  unfold blkd7_2_33
  exact List.forall_mem_cons.2 ⟨subd7_2_1056, List.forall_mem_cons.2 ⟨subd7_2_1057, List.forall_mem_cons.2 ⟨subd7_2_1058, List.forall_mem_cons.2 ⟨subd7_2_1059, List.forall_mem_cons.2 ⟨subd7_2_1060, List.forall_mem_cons.2 ⟨subd7_2_1061, List.forall_mem_cons.2 ⟨subd7_2_1062, List.forall_mem_cons.2 ⟨subd7_2_1063, List.forall_mem_cons.2 ⟨subd7_2_1064, List.forall_mem_cons.2 ⟨subd7_2_1065, List.forall_mem_cons.2 ⟨subd7_2_1066, List.forall_mem_cons.2 ⟨subd7_2_1067, List.forall_mem_cons.2 ⟨subd7_2_1068, List.forall_mem_cons.2 ⟨subd7_2_1069, List.forall_mem_cons.2 ⟨subd7_2_1070, List.forall_mem_cons.2 ⟨subd7_2_1071, List.forall_mem_cons.2 ⟨subd7_2_1072, List.forall_mem_cons.2 ⟨subd7_2_1073, List.forall_mem_cons.2 ⟨subd7_2_1074, List.forall_mem_cons.2 ⟨subd7_2_1075, List.forall_mem_cons.2 ⟨subd7_2_1076, List.forall_mem_cons.2 ⟨subd7_2_1077, List.forall_mem_cons.2 ⟨subd7_2_1078, List.forall_mem_cons.2 ⟨subd7_2_1079, List.forall_mem_cons.2 ⟨subd7_2_1080, List.forall_mem_cons.2 ⟨subd7_2_1081, List.forall_mem_cons.2 ⟨subd7_2_1082, List.forall_mem_cons.2 ⟨subd7_2_1083, List.forall_mem_cons.2 ⟨subd7_2_1084, List.forall_mem_cons.2 ⟨subd7_2_1085, List.forall_mem_cons.2 ⟨subd7_2_1086, List.forall_mem_cons.2 ⟨subd7_2_1087, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_1088 : subd7_2 [2, 3, 0] = true := by decide +kernel
theorem subd7_2_1089 : subd7_2 [2, 3, 1] = true := by decide +kernel
theorem subd7_2_1090 : subd7_2 [2, 3, 2] = true := by decide +kernel
theorem subd7_2_1091 : subd7_2 [2, 3, 3] = true := by decide +kernel
theorem subd7_2_1092 : subd7_2 [2, 3, 4] = true := by decide +kernel
theorem subd7_2_1093 : subd7_2 [2, 3, 5] = true := by decide +kernel
theorem subd7_2_1094 : subd7_2 [2, 4] = true := by decide +kernel
theorem subd7_2_1095 : subd7_2 [2, 5] = true := by decide +kernel
theorem subd7_2_1096 : subd7_2 [3, -7] = true := by decide +kernel
theorem subd7_2_1097 : subd7_2 [3, -6] = true := by decide +kernel
theorem subd7_2_1098 : subd7_2 [3, -5] = true := by decide +kernel
theorem subd7_2_1099 : subd7_2 [3, -4, -7] = true := by decide +kernel
theorem subd7_2_1100 : subd7_2 [3, -4, -6] = true := by decide +kernel
theorem subd7_2_1101 : subd7_2 [3, -4, -5] = true := by decide +kernel
theorem subd7_2_1102 : subd7_2 [3, -4, -4] = true := by decide +kernel
theorem subd7_2_1103 : subd7_2 [3, -4, -3] = true := by decide +kernel
theorem subd7_2_1104 : subd7_2 [3, -4, -2] = true := by decide +kernel
theorem subd7_2_1105 : subd7_2 [3, -4, -1] = true := by decide +kernel
theorem subd7_2_1106 : subd7_2 [3, -4, 0] = true := by decide +kernel
theorem subd7_2_1107 : subd7_2 [3, -4, 1] = true := by decide +kernel
theorem subd7_2_1108 : subd7_2 [3, -4, 2] = true := by decide +kernel
theorem subd7_2_1109 : subd7_2 [3, -4, 3] = true := by decide +kernel
theorem subd7_2_1110 : subd7_2 [3, -4, 4] = true := by decide +kernel
theorem subd7_2_1111 : subd7_2 [3, -4, 5] = true := by decide +kernel
theorem subd7_2_1112 : subd7_2 [3, -4, 6] = true := by decide +kernel
theorem subd7_2_1113 : subd7_2 [3, -4, 7] = true := by decide +kernel
theorem subd7_2_1114 : subd7_2 [3, -4, 8] = true := by decide +kernel
theorem subd7_2_1115 : subd7_2 [3, -3, -8] = true := by decide +kernel
theorem subd7_2_1116 : subd7_2 [3, -3, -7] = true := by decide +kernel
theorem subd7_2_1117 : subd7_2 [3, -3, -6] = true := by decide +kernel
theorem subd7_2_1118 : subd7_2 [3, -3, -5] = true := by decide +kernel
theorem subd7_2_1119 : subd7_2 [3, -3, -4] = true := by decide +kernel
theorem sbd7_2_34 : ∀ q ∈ blkd7_2_34, subd7_2 q = true := by
  unfold blkd7_2_34
  exact List.forall_mem_cons.2 ⟨subd7_2_1088, List.forall_mem_cons.2 ⟨subd7_2_1089, List.forall_mem_cons.2 ⟨subd7_2_1090, List.forall_mem_cons.2 ⟨subd7_2_1091, List.forall_mem_cons.2 ⟨subd7_2_1092, List.forall_mem_cons.2 ⟨subd7_2_1093, List.forall_mem_cons.2 ⟨subd7_2_1094, List.forall_mem_cons.2 ⟨subd7_2_1095, List.forall_mem_cons.2 ⟨subd7_2_1096, List.forall_mem_cons.2 ⟨subd7_2_1097, List.forall_mem_cons.2 ⟨subd7_2_1098, List.forall_mem_cons.2 ⟨subd7_2_1099, List.forall_mem_cons.2 ⟨subd7_2_1100, List.forall_mem_cons.2 ⟨subd7_2_1101, List.forall_mem_cons.2 ⟨subd7_2_1102, List.forall_mem_cons.2 ⟨subd7_2_1103, List.forall_mem_cons.2 ⟨subd7_2_1104, List.forall_mem_cons.2 ⟨subd7_2_1105, List.forall_mem_cons.2 ⟨subd7_2_1106, List.forall_mem_cons.2 ⟨subd7_2_1107, List.forall_mem_cons.2 ⟨subd7_2_1108, List.forall_mem_cons.2 ⟨subd7_2_1109, List.forall_mem_cons.2 ⟨subd7_2_1110, List.forall_mem_cons.2 ⟨subd7_2_1111, List.forall_mem_cons.2 ⟨subd7_2_1112, List.forall_mem_cons.2 ⟨subd7_2_1113, List.forall_mem_cons.2 ⟨subd7_2_1114, List.forall_mem_cons.2 ⟨subd7_2_1115, List.forall_mem_cons.2 ⟨subd7_2_1116, List.forall_mem_cons.2 ⟨subd7_2_1117, List.forall_mem_cons.2 ⟨subd7_2_1118, List.forall_mem_cons.2 ⟨subd7_2_1119, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_1120 : subd7_2 [3, -3, -3] = true := by decide +kernel
theorem subd7_2_1121 : subd7_2 [3, -3, -2] = true := by decide +kernel
theorem subd7_2_1122 : subd7_2 [3, -3, -1] = true := by decide +kernel
theorem subd7_2_1123 : subd7_2 [3, -3, 0] = true := by decide +kernel
theorem subd7_2_1124 : subd7_2 [3, -3, 1] = true := by decide +kernel
theorem subd7_2_1125 : subd7_2 [3, -3, 2] = true := by decide +kernel
theorem subd7_2_1126 : subd7_2 [3, -3, 3] = true := by decide +kernel
theorem subd7_2_1127 : subd7_2 [3, -3, 4] = true := by decide +kernel
theorem subd7_2_1128 : subd7_2 [3, -3, 5] = true := by decide +kernel
theorem subd7_2_1129 : subd7_2 [3, -3, 6] = true := by decide +kernel
theorem subd7_2_1130 : subd7_2 [3, -3, 7] = true := by decide +kernel
theorem subd7_2_1131 : subd7_2 [3, -3, 8] = true := by decide +kernel
theorem subd7_2_1132 : subd7_2 [3, -2, -9] = true := by decide +kernel
theorem subd7_2_1133 : subd7_2 [3, -2, -8] = true := by decide +kernel
theorem subd7_2_1134 : subd7_2 [3, -2, -7] = true := by decide +kernel
theorem subd7_2_1135 : subd7_2 [3, -2, -6] = true := by decide +kernel
theorem subd7_2_1136 : subd7_2 [3, -2, -5] = true := by decide +kernel
theorem subd7_2_1137 : subd7_2 [3, -2, -4] = true := by decide +kernel
theorem subd7_2_1138 : subd7_2 [3, -2, -3] = true := by decide +kernel
theorem subd7_2_1139 : subd7_2 [3, -2, -2] = true := by decide +kernel
theorem subd7_2_1140 : subd7_2 [3, -2, -1] = true := by decide +kernel
theorem subd7_2_1141 : subd7_2 [3, -2, 0] = true := by decide +kernel
theorem subd7_2_1142 : subd7_2 [3, -2, 1] = true := by decide +kernel
theorem subd7_2_1143 : subd7_2 [3, -2, 2] = true := by decide +kernel
theorem subd7_2_1144 : subd7_2 [3, -2, 3] = true := by decide +kernel
theorem subd7_2_1145 : subd7_2 [3, -2, 4] = true := by decide +kernel
theorem subd7_2_1146 : subd7_2 [3, -2, 5] = true := by decide +kernel
theorem subd7_2_1147 : subd7_2 [3, -2, 6] = true := by decide +kernel
theorem subd7_2_1148 : subd7_2 [3, -2, 7] = true := by decide +kernel
theorem subd7_2_1149 : subd7_2 [3, -2, 8] = true := by decide +kernel
theorem subd7_2_1150 : subd7_2 [3, -1, -9] = true := by decide +kernel
theorem subd7_2_1151 : subd7_2 [3, -1, -8] = true := by decide +kernel
theorem sbd7_2_35 : ∀ q ∈ blkd7_2_35, subd7_2 q = true := by
  unfold blkd7_2_35
  exact List.forall_mem_cons.2 ⟨subd7_2_1120, List.forall_mem_cons.2 ⟨subd7_2_1121, List.forall_mem_cons.2 ⟨subd7_2_1122, List.forall_mem_cons.2 ⟨subd7_2_1123, List.forall_mem_cons.2 ⟨subd7_2_1124, List.forall_mem_cons.2 ⟨subd7_2_1125, List.forall_mem_cons.2 ⟨subd7_2_1126, List.forall_mem_cons.2 ⟨subd7_2_1127, List.forall_mem_cons.2 ⟨subd7_2_1128, List.forall_mem_cons.2 ⟨subd7_2_1129, List.forall_mem_cons.2 ⟨subd7_2_1130, List.forall_mem_cons.2 ⟨subd7_2_1131, List.forall_mem_cons.2 ⟨subd7_2_1132, List.forall_mem_cons.2 ⟨subd7_2_1133, List.forall_mem_cons.2 ⟨subd7_2_1134, List.forall_mem_cons.2 ⟨subd7_2_1135, List.forall_mem_cons.2 ⟨subd7_2_1136, List.forall_mem_cons.2 ⟨subd7_2_1137, List.forall_mem_cons.2 ⟨subd7_2_1138, List.forall_mem_cons.2 ⟨subd7_2_1139, List.forall_mem_cons.2 ⟨subd7_2_1140, List.forall_mem_cons.2 ⟨subd7_2_1141, List.forall_mem_cons.2 ⟨subd7_2_1142, List.forall_mem_cons.2 ⟨subd7_2_1143, List.forall_mem_cons.2 ⟨subd7_2_1144, List.forall_mem_cons.2 ⟨subd7_2_1145, List.forall_mem_cons.2 ⟨subd7_2_1146, List.forall_mem_cons.2 ⟨subd7_2_1147, List.forall_mem_cons.2 ⟨subd7_2_1148, List.forall_mem_cons.2 ⟨subd7_2_1149, List.forall_mem_cons.2 ⟨subd7_2_1150, List.forall_mem_cons.2 ⟨subd7_2_1151, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_1152 : subd7_2 [3, -1, -7] = true := by decide +kernel
theorem subd7_2_1153 : subd7_2 [3, -1, -6] = true := by decide +kernel
theorem subd7_2_1154 : subd7_2 [3, -1, -5] = true := by decide +kernel
theorem subd7_2_1155 : subd7_2 [3, -1, -4] = true := by decide +kernel
theorem subd7_2_1156 : subd7_2 [3, -1, -3] = true := by decide +kernel
theorem subd7_2_1157 : subd7_2 [3, -1, -2] = true := by decide +kernel
theorem subd7_2_1158 : subd7_2 [3, -1, -1] = true := by decide +kernel
theorem subd7_2_1159 : subd7_2 [3, -1, 0] = true := by decide +kernel
theorem subd7_2_1160 : subd7_2 [3, -1, 1] = true := by decide +kernel
theorem subd7_2_1161 : subd7_2 [3, -1, 2] = true := by decide +kernel
theorem subd7_2_1162 : subd7_2 [3, -1, 3] = true := by decide +kernel
theorem subd7_2_1163 : subd7_2 [3, -1, 4] = true := by decide +kernel
theorem subd7_2_1164 : subd7_2 [3, -1, 5] = true := by decide +kernel
theorem subd7_2_1165 : subd7_2 [3, -1, 6] = true := by decide +kernel
theorem subd7_2_1166 : subd7_2 [3, -1, 7] = true := by decide +kernel
theorem subd7_2_1167 : subd7_2 [3, -1, 8] = true := by decide +kernel
theorem subd7_2_1168 : subd7_2 [3, 0, -10] = true := by decide +kernel
theorem subd7_2_1169 : subd7_2 [3, 0, -9] = true := by decide +kernel
theorem subd7_2_1170 : subd7_2 [3, 0, -8] = true := by decide +kernel
theorem subd7_2_1171 : subd7_2 [3, 0, -7] = true := by decide +kernel
theorem subd7_2_1172 : subd7_2 [3, 0, -6] = true := by decide +kernel
theorem subd7_2_1173 : subd7_2 [3, 0, -5] = true := by decide +kernel
theorem subd7_2_1174 : subd7_2 [3, 0, -4] = true := by decide +kernel
theorem subd7_2_1175 : subd7_2 [3, 0, -3] = true := by decide +kernel
theorem subd7_2_1176 : subd7_2 [3, 0, -2] = true := by decide +kernel
theorem subd7_2_1177 : subd7_2 [3, 0, -1] = true := by decide +kernel
theorem subd7_2_1178 : subd7_2 [3, 0, 0] = true := by decide +kernel
theorem subd7_2_1179 : subd7_2 [3, 0, 1] = true := by decide +kernel
theorem subd7_2_1180 : subd7_2 [3, 0, 2] = true := by decide +kernel
theorem subd7_2_1181 : subd7_2 [3, 0, 3] = true := by decide +kernel
theorem subd7_2_1182 : subd7_2 [3, 0, 4] = true := by decide +kernel
theorem subd7_2_1183 : subd7_2 [3, 0, 5] = true := by decide +kernel
theorem sbd7_2_36 : ∀ q ∈ blkd7_2_36, subd7_2 q = true := by
  unfold blkd7_2_36
  exact List.forall_mem_cons.2 ⟨subd7_2_1152, List.forall_mem_cons.2 ⟨subd7_2_1153, List.forall_mem_cons.2 ⟨subd7_2_1154, List.forall_mem_cons.2 ⟨subd7_2_1155, List.forall_mem_cons.2 ⟨subd7_2_1156, List.forall_mem_cons.2 ⟨subd7_2_1157, List.forall_mem_cons.2 ⟨subd7_2_1158, List.forall_mem_cons.2 ⟨subd7_2_1159, List.forall_mem_cons.2 ⟨subd7_2_1160, List.forall_mem_cons.2 ⟨subd7_2_1161, List.forall_mem_cons.2 ⟨subd7_2_1162, List.forall_mem_cons.2 ⟨subd7_2_1163, List.forall_mem_cons.2 ⟨subd7_2_1164, List.forall_mem_cons.2 ⟨subd7_2_1165, List.forall_mem_cons.2 ⟨subd7_2_1166, List.forall_mem_cons.2 ⟨subd7_2_1167, List.forall_mem_cons.2 ⟨subd7_2_1168, List.forall_mem_cons.2 ⟨subd7_2_1169, List.forall_mem_cons.2 ⟨subd7_2_1170, List.forall_mem_cons.2 ⟨subd7_2_1171, List.forall_mem_cons.2 ⟨subd7_2_1172, List.forall_mem_cons.2 ⟨subd7_2_1173, List.forall_mem_cons.2 ⟨subd7_2_1174, List.forall_mem_cons.2 ⟨subd7_2_1175, List.forall_mem_cons.2 ⟨subd7_2_1176, List.forall_mem_cons.2 ⟨subd7_2_1177, List.forall_mem_cons.2 ⟨subd7_2_1178, List.forall_mem_cons.2 ⟨subd7_2_1179, List.forall_mem_cons.2 ⟨subd7_2_1180, List.forall_mem_cons.2 ⟨subd7_2_1181, List.forall_mem_cons.2 ⟨subd7_2_1182, List.forall_mem_cons.2 ⟨subd7_2_1183, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_1184 : subd7_2 [3, 0, 6] = true := by decide +kernel
theorem subd7_2_1185 : subd7_2 [3, 0, 7] = true := by decide +kernel
theorem subd7_2_1186 : subd7_2 [3, 1, -10] = true := by decide +kernel
theorem subd7_2_1187 : subd7_2 [3, 1, -9] = true := by decide +kernel
theorem subd7_2_1188 : subd7_2 [3, 1, -8] = true := by decide +kernel
theorem subd7_2_1189 : subd7_2 [3, 1, -7] = true := by decide +kernel
theorem subd7_2_1190 : subd7_2 [3, 1, -6] = true := by decide +kernel
theorem subd7_2_1191 : subd7_2 [3, 1, -5] = true := by decide +kernel
theorem subd7_2_1192 : subd7_2 [3, 1, -4] = true := by decide +kernel
theorem subd7_2_1193 : subd7_2 [3, 1, -3] = true := by decide +kernel
theorem subd7_2_1194 : subd7_2 [3, 1, -2] = true := by decide +kernel
theorem subd7_2_1195 : subd7_2 [3, 1, -1] = true := by decide +kernel
theorem subd7_2_1196 : subd7_2 [3, 1, 0] = true := by decide +kernel
theorem subd7_2_1197 : subd7_2 [3, 1, 1] = true := by decide +kernel
theorem subd7_2_1198 : subd7_2 [3, 1, 2] = true := by decide +kernel
theorem subd7_2_1199 : subd7_2 [3, 1, 3] = true := by decide +kernel
theorem subd7_2_1200 : subd7_2 [3, 1, 4] = true := by decide +kernel
theorem subd7_2_1201 : subd7_2 [3, 1, 5] = true := by decide +kernel
theorem subd7_2_1202 : subd7_2 [3, 1, 6] = true := by decide +kernel
theorem subd7_2_1203 : subd7_2 [3, 2, -9] = true := by decide +kernel
theorem subd7_2_1204 : subd7_2 [3, 2, -8] = true := by decide +kernel
theorem subd7_2_1205 : subd7_2 [3, 2, -7] = true := by decide +kernel
theorem subd7_2_1206 : subd7_2 [3, 2, -6] = true := by decide +kernel
theorem subd7_2_1207 : subd7_2 [3, 2, -5] = true := by decide +kernel
theorem subd7_2_1208 : subd7_2 [3, 2, -4] = true := by decide +kernel
theorem subd7_2_1209 : subd7_2 [3, 2, -3] = true := by decide +kernel
theorem subd7_2_1210 : subd7_2 [3, 2, -2] = true := by decide +kernel
theorem subd7_2_1211 : subd7_2 [3, 2, -1] = true := by decide +kernel
theorem subd7_2_1212 : subd7_2 [3, 2, 0] = true := by decide +kernel
theorem subd7_2_1213 : subd7_2 [3, 2, 1] = true := by decide +kernel
theorem subd7_2_1214 : subd7_2 [3, 2, 2] = true := by decide +kernel
theorem subd7_2_1215 : subd7_2 [3, 2, 3] = true := by decide +kernel
theorem sbd7_2_37 : ∀ q ∈ blkd7_2_37, subd7_2 q = true := by
  unfold blkd7_2_37
  exact List.forall_mem_cons.2 ⟨subd7_2_1184, List.forall_mem_cons.2 ⟨subd7_2_1185, List.forall_mem_cons.2 ⟨subd7_2_1186, List.forall_mem_cons.2 ⟨subd7_2_1187, List.forall_mem_cons.2 ⟨subd7_2_1188, List.forall_mem_cons.2 ⟨subd7_2_1189, List.forall_mem_cons.2 ⟨subd7_2_1190, List.forall_mem_cons.2 ⟨subd7_2_1191, List.forall_mem_cons.2 ⟨subd7_2_1192, List.forall_mem_cons.2 ⟨subd7_2_1193, List.forall_mem_cons.2 ⟨subd7_2_1194, List.forall_mem_cons.2 ⟨subd7_2_1195, List.forall_mem_cons.2 ⟨subd7_2_1196, List.forall_mem_cons.2 ⟨subd7_2_1197, List.forall_mem_cons.2 ⟨subd7_2_1198, List.forall_mem_cons.2 ⟨subd7_2_1199, List.forall_mem_cons.2 ⟨subd7_2_1200, List.forall_mem_cons.2 ⟨subd7_2_1201, List.forall_mem_cons.2 ⟨subd7_2_1202, List.forall_mem_cons.2 ⟨subd7_2_1203, List.forall_mem_cons.2 ⟨subd7_2_1204, List.forall_mem_cons.2 ⟨subd7_2_1205, List.forall_mem_cons.2 ⟨subd7_2_1206, List.forall_mem_cons.2 ⟨subd7_2_1207, List.forall_mem_cons.2 ⟨subd7_2_1208, List.forall_mem_cons.2 ⟨subd7_2_1209, List.forall_mem_cons.2 ⟨subd7_2_1210, List.forall_mem_cons.2 ⟨subd7_2_1211, List.forall_mem_cons.2 ⟨subd7_2_1212, List.forall_mem_cons.2 ⟨subd7_2_1213, List.forall_mem_cons.2 ⟨subd7_2_1214, List.forall_mem_cons.2 ⟨subd7_2_1215, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_1216 : subd7_2 [3, 2, 4] = true := by decide +kernel
theorem subd7_2_1217 : subd7_2 [3, 2, 5] = true := by decide +kernel
theorem subd7_2_1218 : subd7_2 [3, 3] = true := by decide +kernel
theorem subd7_2_1219 : subd7_2 [3, 4] = true := by decide +kernel
theorem subd7_2_1220 : subd7_2 [4, -6] = true := by decide +kernel
theorem subd7_2_1221 : subd7_2 [4, -5] = true := by decide +kernel
theorem subd7_2_1222 : subd7_2 [4, -4] = true := by decide +kernel
theorem subd7_2_1223 : subd7_2 [4, -3, -7] = true := by decide +kernel
theorem subd7_2_1224 : subd7_2 [4, -3, -6] = true := by decide +kernel
theorem subd7_2_1225 : subd7_2 [4, -3, -5] = true := by decide +kernel
theorem subd7_2_1226 : subd7_2 [4, -3, -4] = true := by decide +kernel
theorem subd7_2_1227 : subd7_2 [4, -3, -3] = true := by decide +kernel
theorem subd7_2_1228 : subd7_2 [4, -3, -2] = true := by decide +kernel
theorem subd7_2_1229 : subd7_2 [4, -3, -1] = true := by decide +kernel
theorem subd7_2_1230 : subd7_2 [4, -3, 0] = true := by decide +kernel
theorem subd7_2_1231 : subd7_2 [4, -3, 1] = true := by decide +kernel
theorem subd7_2_1232 : subd7_2 [4, -3, 2] = true := by decide +kernel
theorem subd7_2_1233 : subd7_2 [4, -3, 3] = true := by decide +kernel
theorem subd7_2_1234 : subd7_2 [4, -3, 4] = true := by decide +kernel
theorem subd7_2_1235 : subd7_2 [4, -3, 5] = true := by decide +kernel
theorem subd7_2_1236 : subd7_2 [4, -3, 6] = true := by decide +kernel
theorem subd7_2_1237 : subd7_2 [4, -3, 7] = true := by decide +kernel
theorem subd7_2_1238 : subd7_2 [4, -2, -8] = true := by decide +kernel
theorem subd7_2_1239 : subd7_2 [4, -2, -7] = true := by decide +kernel
theorem subd7_2_1240 : subd7_2 [4, -2, -6] = true := by decide +kernel
theorem subd7_2_1241 : subd7_2 [4, -2, -5] = true := by decide +kernel
theorem subd7_2_1242 : subd7_2 [4, -2, -4] = true := by decide +kernel
theorem subd7_2_1243 : subd7_2 [4, -2, -3] = true := by decide +kernel
theorem subd7_2_1244 : subd7_2 [4, -2, -2] = true := by decide +kernel
theorem subd7_2_1245 : subd7_2 [4, -2, -1] = true := by decide +kernel
theorem subd7_2_1246 : subd7_2 [4, -2, 0] = true := by decide +kernel
theorem subd7_2_1247 : subd7_2 [4, -2, 1] = true := by decide +kernel
theorem sbd7_2_38 : ∀ q ∈ blkd7_2_38, subd7_2 q = true := by
  unfold blkd7_2_38
  exact List.forall_mem_cons.2 ⟨subd7_2_1216, List.forall_mem_cons.2 ⟨subd7_2_1217, List.forall_mem_cons.2 ⟨subd7_2_1218, List.forall_mem_cons.2 ⟨subd7_2_1219, List.forall_mem_cons.2 ⟨subd7_2_1220, List.forall_mem_cons.2 ⟨subd7_2_1221, List.forall_mem_cons.2 ⟨subd7_2_1222, List.forall_mem_cons.2 ⟨subd7_2_1223, List.forall_mem_cons.2 ⟨subd7_2_1224, List.forall_mem_cons.2 ⟨subd7_2_1225, List.forall_mem_cons.2 ⟨subd7_2_1226, List.forall_mem_cons.2 ⟨subd7_2_1227, List.forall_mem_cons.2 ⟨subd7_2_1228, List.forall_mem_cons.2 ⟨subd7_2_1229, List.forall_mem_cons.2 ⟨subd7_2_1230, List.forall_mem_cons.2 ⟨subd7_2_1231, List.forall_mem_cons.2 ⟨subd7_2_1232, List.forall_mem_cons.2 ⟨subd7_2_1233, List.forall_mem_cons.2 ⟨subd7_2_1234, List.forall_mem_cons.2 ⟨subd7_2_1235, List.forall_mem_cons.2 ⟨subd7_2_1236, List.forall_mem_cons.2 ⟨subd7_2_1237, List.forall_mem_cons.2 ⟨subd7_2_1238, List.forall_mem_cons.2 ⟨subd7_2_1239, List.forall_mem_cons.2 ⟨subd7_2_1240, List.forall_mem_cons.2 ⟨subd7_2_1241, List.forall_mem_cons.2 ⟨subd7_2_1242, List.forall_mem_cons.2 ⟨subd7_2_1243, List.forall_mem_cons.2 ⟨subd7_2_1244, List.forall_mem_cons.2 ⟨subd7_2_1245, List.forall_mem_cons.2 ⟨subd7_2_1246, List.forall_mem_cons.2 ⟨subd7_2_1247, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_1248 : subd7_2 [4, -2, 2] = true := by decide +kernel
theorem subd7_2_1249 : subd7_2 [4, -2, 3] = true := by decide +kernel
theorem subd7_2_1250 : subd7_2 [4, -2, 4] = true := by decide +kernel
theorem subd7_2_1251 : subd7_2 [4, -2, 5] = true := by decide +kernel
theorem subd7_2_1252 : subd7_2 [4, -2, 6] = true := by decide +kernel
theorem subd7_2_1253 : subd7_2 [4, -2, 7] = true := by decide +kernel
theorem subd7_2_1254 : subd7_2 [4, -1, -8] = true := by decide +kernel
theorem subd7_2_1255 : subd7_2 [4, -1, -7] = true := by decide +kernel
theorem subd7_2_1256 : subd7_2 [4, -1, -6] = true := by decide +kernel
theorem subd7_2_1257 : subd7_2 [4, -1, -5] = true := by decide +kernel
theorem subd7_2_1258 : subd7_2 [4, -1, -4] = true := by decide +kernel
theorem subd7_2_1259 : subd7_2 [4, -1, -3] = true := by decide +kernel
theorem subd7_2_1260 : subd7_2 [4, -1, -2] = true := by decide +kernel
theorem subd7_2_1261 : subd7_2 [4, -1, -1] = true := by decide +kernel
theorem subd7_2_1262 : subd7_2 [4, -1, 0] = true := by decide +kernel
theorem subd7_2_1263 : subd7_2 [4, -1, 1] = true := by decide +kernel
theorem subd7_2_1264 : subd7_2 [4, -1, 2] = true := by decide +kernel
theorem subd7_2_1265 : subd7_2 [4, -1, 3] = true := by decide +kernel
theorem subd7_2_1266 : subd7_2 [4, -1, 4] = true := by decide +kernel
theorem subd7_2_1267 : subd7_2 [4, -1, 5] = true := by decide +kernel
theorem subd7_2_1268 : subd7_2 [4, -1, 6] = true := by decide +kernel
theorem subd7_2_1269 : subd7_2 [4, 0, -8] = true := by decide +kernel
theorem subd7_2_1270 : subd7_2 [4, 0, -7] = true := by decide +kernel
theorem subd7_2_1271 : subd7_2 [4, 0, -6] = true := by decide +kernel
theorem subd7_2_1272 : subd7_2 [4, 0, -5] = true := by decide +kernel
theorem subd7_2_1273 : subd7_2 [4, 0, -4] = true := by decide +kernel
theorem subd7_2_1274 : subd7_2 [4, 0, -3] = true := by decide +kernel
theorem subd7_2_1275 : subd7_2 [4, 0, -2] = true := by decide +kernel
theorem subd7_2_1276 : subd7_2 [4, 0, -1] = true := by decide +kernel
theorem subd7_2_1277 : subd7_2 [4, 0, 0] = true := by decide +kernel
theorem subd7_2_1278 : subd7_2 [4, 0, 1] = true := by decide +kernel
theorem subd7_2_1279 : subd7_2 [4, 0, 2] = true := by decide +kernel
theorem sbd7_2_39 : ∀ q ∈ blkd7_2_39, subd7_2 q = true := by
  unfold blkd7_2_39
  exact List.forall_mem_cons.2 ⟨subd7_2_1248, List.forall_mem_cons.2 ⟨subd7_2_1249, List.forall_mem_cons.2 ⟨subd7_2_1250, List.forall_mem_cons.2 ⟨subd7_2_1251, List.forall_mem_cons.2 ⟨subd7_2_1252, List.forall_mem_cons.2 ⟨subd7_2_1253, List.forall_mem_cons.2 ⟨subd7_2_1254, List.forall_mem_cons.2 ⟨subd7_2_1255, List.forall_mem_cons.2 ⟨subd7_2_1256, List.forall_mem_cons.2 ⟨subd7_2_1257, List.forall_mem_cons.2 ⟨subd7_2_1258, List.forall_mem_cons.2 ⟨subd7_2_1259, List.forall_mem_cons.2 ⟨subd7_2_1260, List.forall_mem_cons.2 ⟨subd7_2_1261, List.forall_mem_cons.2 ⟨subd7_2_1262, List.forall_mem_cons.2 ⟨subd7_2_1263, List.forall_mem_cons.2 ⟨subd7_2_1264, List.forall_mem_cons.2 ⟨subd7_2_1265, List.forall_mem_cons.2 ⟨subd7_2_1266, List.forall_mem_cons.2 ⟨subd7_2_1267, List.forall_mem_cons.2 ⟨subd7_2_1268, List.forall_mem_cons.2 ⟨subd7_2_1269, List.forall_mem_cons.2 ⟨subd7_2_1270, List.forall_mem_cons.2 ⟨subd7_2_1271, List.forall_mem_cons.2 ⟨subd7_2_1272, List.forall_mem_cons.2 ⟨subd7_2_1273, List.forall_mem_cons.2 ⟨subd7_2_1274, List.forall_mem_cons.2 ⟨subd7_2_1275, List.forall_mem_cons.2 ⟨subd7_2_1276, List.forall_mem_cons.2 ⟨subd7_2_1277, List.forall_mem_cons.2 ⟨subd7_2_1278, List.forall_mem_cons.2 ⟨subd7_2_1279, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_1280 : subd7_2 [4, 0, 3] = true := by decide +kernel
theorem subd7_2_1281 : subd7_2 [4, 0, 4] = true := by decide +kernel
theorem subd7_2_1282 : subd7_2 [4, 0, 5] = true := by decide +kernel
theorem subd7_2_1283 : subd7_2 [4, 1] = true := by decide +kernel
theorem subd7_2_1284 : subd7_2 [4, 2] = true := by decide +kernel
theorem subd7_2_1285 : subd7_2 [5, -5] = true := by decide +kernel
theorem subd7_2_1286 : subd7_2 [5, -4] = true := by decide +kernel
theorem subd7_2_1287 : subd7_2 [5, -3] = true := by decide +kernel
theorem subd7_2_1288 : subd7_2 [5, -2] = true := by decide +kernel
theorem subd7_2_1289 : subd7_2 [5, -1] = true := by decide +kernel
theorem subd7_2_1290 : subd7_2 [5, 0] = true := by decide +kernel
theorem sbd7_2_40 : ∀ q ∈ blkd7_2_40, subd7_2 q = true := by
  unfold blkd7_2_40
  exact List.forall_mem_cons.2 ⟨subd7_2_1280, List.forall_mem_cons.2 ⟨subd7_2_1281, List.forall_mem_cons.2 ⟨subd7_2_1282, List.forall_mem_cons.2 ⟨subd7_2_1283, List.forall_mem_cons.2 ⟨subd7_2_1284, List.forall_mem_cons.2 ⟨subd7_2_1285, List.forall_mem_cons.2 ⟨subd7_2_1286, List.forall_mem_cons.2 ⟨subd7_2_1287, List.forall_mem_cons.2 ⟨subd7_2_1288, List.forall_mem_cons.2 ⟨subd7_2_1289, List.forall_mem_cons.2 ⟨subd7_2_1290, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_3 : ldCheck G d7_3.U d7_3.ms ldd7_3 = true := by decide +kernel
theorem pre_okd7_3 : subPre G cell7 d7_3 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C121
