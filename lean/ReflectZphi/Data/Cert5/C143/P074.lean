import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd19_3_896 : subd19_3 [0, 1, 8] = true := by decide +kernel
theorem subd19_3_897 : subd19_3 [0, 2, -10] = true := by decide +kernel
theorem subd19_3_898 : subd19_3 [0, 2, -9] = true := by decide +kernel
theorem subd19_3_899 : subd19_3 [0, 2, -8] = true := by decide +kernel
theorem subd19_3_900 : subd19_3 [0, 2, -7] = true := by decide +kernel
theorem subd19_3_901 : subd19_3 [0, 2, -6] = true := by decide +kernel
theorem subd19_3_902 : subd19_3 [0, 2, -5] = true := by decide +kernel
theorem subd19_3_903 : subd19_3 [0, 2, -4] = true := by decide +kernel
theorem subd19_3_904 : subd19_3 [0, 2, -3] = true := by decide +kernel
theorem subd19_3_905 : subd19_3 [0, 2, -2] = true := by decide +kernel
theorem subd19_3_906 : subd19_3 [0, 2, -1] = true := by decide +kernel
theorem subd19_3_907 : subd19_3 [0, 2, 0] = true := by decide +kernel
theorem subd19_3_908 : subd19_3 [0, 2, 1] = true := by decide +kernel
theorem subd19_3_909 : subd19_3 [0, 2, 2] = true := by decide +kernel
theorem subd19_3_910 : subd19_3 [0, 2, 3] = true := by decide +kernel
theorem subd19_3_911 : subd19_3 [0, 2, 4] = true := by decide +kernel
theorem subd19_3_912 : subd19_3 [0, 2, 5] = true := by decide +kernel
theorem subd19_3_913 : subd19_3 [0, 2, 6] = true := by decide +kernel
theorem subd19_3_914 : subd19_3 [0, 2, 7] = true := by decide +kernel
theorem subd19_3_915 : subd19_3 [0, 3, -10] = true := by decide +kernel
theorem subd19_3_916 : subd19_3 [0, 3, -9] = true := by decide +kernel
theorem subd19_3_917 : subd19_3 [0, 3, -8] = true := by decide +kernel
theorem subd19_3_918 : subd19_3 [0, 3, -7] = true := by decide +kernel
theorem subd19_3_919 : subd19_3 [0, 3, -6] = true := by decide +kernel
theorem subd19_3_920 : subd19_3 [0, 3, -5] = true := by decide +kernel
theorem subd19_3_921 : subd19_3 [0, 3, -4] = true := by decide +kernel
theorem subd19_3_922 : subd19_3 [0, 3, -3] = true := by decide +kernel
theorem subd19_3_923 : subd19_3 [0, 3, -2] = true := by decide +kernel
theorem subd19_3_924 : subd19_3 [0, 3, -1] = true := by decide +kernel
theorem subd19_3_925 : subd19_3 [0, 3, 0] = true := by decide +kernel
theorem subd19_3_926 : subd19_3 [0, 3, 1] = true := by decide +kernel
theorem subd19_3_927 : subd19_3 [0, 3, 2] = true := by decide +kernel
theorem sbd19_3_28 : ∀ q ∈ blkd19_3_28, subd19_3 q = true := by
  unfold blkd19_3_28
  exact List.forall_mem_cons.2 ⟨subd19_3_896, List.forall_mem_cons.2 ⟨subd19_3_897, List.forall_mem_cons.2 ⟨subd19_3_898, List.forall_mem_cons.2 ⟨subd19_3_899, List.forall_mem_cons.2 ⟨subd19_3_900, List.forall_mem_cons.2 ⟨subd19_3_901, List.forall_mem_cons.2 ⟨subd19_3_902, List.forall_mem_cons.2 ⟨subd19_3_903, List.forall_mem_cons.2 ⟨subd19_3_904, List.forall_mem_cons.2 ⟨subd19_3_905, List.forall_mem_cons.2 ⟨subd19_3_906, List.forall_mem_cons.2 ⟨subd19_3_907, List.forall_mem_cons.2 ⟨subd19_3_908, List.forall_mem_cons.2 ⟨subd19_3_909, List.forall_mem_cons.2 ⟨subd19_3_910, List.forall_mem_cons.2 ⟨subd19_3_911, List.forall_mem_cons.2 ⟨subd19_3_912, List.forall_mem_cons.2 ⟨subd19_3_913, List.forall_mem_cons.2 ⟨subd19_3_914, List.forall_mem_cons.2 ⟨subd19_3_915, List.forall_mem_cons.2 ⟨subd19_3_916, List.forall_mem_cons.2 ⟨subd19_3_917, List.forall_mem_cons.2 ⟨subd19_3_918, List.forall_mem_cons.2 ⟨subd19_3_919, List.forall_mem_cons.2 ⟨subd19_3_920, List.forall_mem_cons.2 ⟨subd19_3_921, List.forall_mem_cons.2 ⟨subd19_3_922, List.forall_mem_cons.2 ⟨subd19_3_923, List.forall_mem_cons.2 ⟨subd19_3_924, List.forall_mem_cons.2 ⟨subd19_3_925, List.forall_mem_cons.2 ⟨subd19_3_926, List.forall_mem_cons.2 ⟨subd19_3_927, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_3_928 : subd19_3 [0, 3, 3] = true := by decide +kernel
theorem subd19_3_929 : subd19_3 [0, 3, 4] = true := by decide +kernel
theorem subd19_3_930 : subd19_3 [0, 3, 5] = true := by decide +kernel
theorem subd19_3_931 : subd19_3 [0, 3, 6] = true := by decide +kernel
theorem subd19_3_932 : subd19_3 [0, 4, -10] = true := by decide +kernel
theorem subd19_3_933 : subd19_3 [0, 4, -9] = true := by decide +kernel
theorem subd19_3_934 : subd19_3 [0, 4, -8] = true := by decide +kernel
theorem subd19_3_935 : subd19_3 [0, 4, -7] = true := by decide +kernel
theorem subd19_3_936 : subd19_3 [0, 4, -6] = true := by decide +kernel
theorem subd19_3_937 : subd19_3 [0, 4, -5] = true := by decide +kernel
theorem subd19_3_938 : subd19_3 [0, 4, -4] = true := by decide +kernel
theorem subd19_3_939 : subd19_3 [0, 4, -3] = true := by decide +kernel
theorem subd19_3_940 : subd19_3 [0, 4, -2] = true := by decide +kernel
theorem subd19_3_941 : subd19_3 [0, 4, -1] = true := by decide +kernel
theorem subd19_3_942 : subd19_3 [0, 4, 0] = true := by decide +kernel
theorem subd19_3_943 : subd19_3 [0, 4, 1] = true := by decide +kernel
theorem subd19_3_944 : subd19_3 [0, 4, 2] = true := by decide +kernel
theorem subd19_3_945 : subd19_3 [0, 4, 3] = true := by decide +kernel
theorem subd19_3_946 : subd19_3 [0, 4, 4] = true := by decide +kernel
theorem subd19_3_947 : subd19_3 [0, 4, 5] = true := by decide +kernel
theorem subd19_3_948 : subd19_3 [0, 5, -10] = true := by decide +kernel
theorem subd19_3_949 : subd19_3 [0, 5, -9] = true := by decide +kernel
theorem subd19_3_950 : subd19_3 [0, 5, -8] = true := by decide +kernel
theorem subd19_3_951 : subd19_3 [0, 5, -7] = true := by decide +kernel
theorem subd19_3_952 : subd19_3 [0, 5, -6] = true := by decide +kernel
theorem subd19_3_953 : subd19_3 [0, 5, -5] = true := by decide +kernel
theorem subd19_3_954 : subd19_3 [0, 5, -4] = true := by decide +kernel
theorem subd19_3_955 : subd19_3 [0, 5, -3] = true := by decide +kernel
theorem subd19_3_956 : subd19_3 [0, 5, -2] = true := by decide +kernel
theorem subd19_3_957 : subd19_3 [0, 5, -1] = true := by decide +kernel
theorem subd19_3_958 : subd19_3 [0, 5, 0] = true := by decide +kernel
theorem subd19_3_959 : subd19_3 [0, 5, 1] = true := by decide +kernel
theorem sbd19_3_29 : ∀ q ∈ blkd19_3_29, subd19_3 q = true := by
  unfold blkd19_3_29
  exact List.forall_mem_cons.2 ⟨subd19_3_928, List.forall_mem_cons.2 ⟨subd19_3_929, List.forall_mem_cons.2 ⟨subd19_3_930, List.forall_mem_cons.2 ⟨subd19_3_931, List.forall_mem_cons.2 ⟨subd19_3_932, List.forall_mem_cons.2 ⟨subd19_3_933, List.forall_mem_cons.2 ⟨subd19_3_934, List.forall_mem_cons.2 ⟨subd19_3_935, List.forall_mem_cons.2 ⟨subd19_3_936, List.forall_mem_cons.2 ⟨subd19_3_937, List.forall_mem_cons.2 ⟨subd19_3_938, List.forall_mem_cons.2 ⟨subd19_3_939, List.forall_mem_cons.2 ⟨subd19_3_940, List.forall_mem_cons.2 ⟨subd19_3_941, List.forall_mem_cons.2 ⟨subd19_3_942, List.forall_mem_cons.2 ⟨subd19_3_943, List.forall_mem_cons.2 ⟨subd19_3_944, List.forall_mem_cons.2 ⟨subd19_3_945, List.forall_mem_cons.2 ⟨subd19_3_946, List.forall_mem_cons.2 ⟨subd19_3_947, List.forall_mem_cons.2 ⟨subd19_3_948, List.forall_mem_cons.2 ⟨subd19_3_949, List.forall_mem_cons.2 ⟨subd19_3_950, List.forall_mem_cons.2 ⟨subd19_3_951, List.forall_mem_cons.2 ⟨subd19_3_952, List.forall_mem_cons.2 ⟨subd19_3_953, List.forall_mem_cons.2 ⟨subd19_3_954, List.forall_mem_cons.2 ⟨subd19_3_955, List.forall_mem_cons.2 ⟨subd19_3_956, List.forall_mem_cons.2 ⟨subd19_3_957, List.forall_mem_cons.2 ⟨subd19_3_958, List.forall_mem_cons.2 ⟨subd19_3_959, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_3_960 : subd19_3 [0, 5, 2] = true := by decide +kernel
theorem subd19_3_961 : subd19_3 [0, 5, 3] = true := by decide +kernel
theorem subd19_3_962 : subd19_3 [0, 5, 4] = true := by decide +kernel
theorem subd19_3_963 : subd19_3 [0, 6] = true := by decide +kernel
theorem subd19_3_964 : subd19_3 [0, 7] = true := by decide +kernel
theorem subd19_3_965 : subd19_3 [0, 8] = true := by decide +kernel
theorem subd19_3_966 : subd19_3 [1, -9] = true := by decide +kernel
theorem subd19_3_967 : subd19_3 [1, -8] = true := by decide +kernel
theorem subd19_3_968 : subd19_3 [1, -7] = true := by decide +kernel
theorem subd19_3_969 : subd19_3 [1, -6] = true := by decide +kernel
theorem subd19_3_970 : subd19_3 [1, -5, -5] = true := by decide +kernel
theorem subd19_3_971 : subd19_3 [1, -5, -4] = true := by decide +kernel
theorem subd19_3_972 : subd19_3 [1, -5, -3] = true := by decide +kernel
theorem subd19_3_973 : subd19_3 [1, -5, -2] = true := by decide +kernel
theorem subd19_3_974 : subd19_3 [1, -5, -1] = true := by decide +kernel
theorem subd19_3_975 : subd19_3 [1, -5, 0] = true := by decide +kernel
theorem subd19_3_976 : subd19_3 [1, -5, 1] = true := by decide +kernel
theorem subd19_3_977 : subd19_3 [1, -5, 2] = true := by decide +kernel
theorem subd19_3_978 : subd19_3 [1, -5, 3] = true := by decide +kernel
theorem subd19_3_979 : subd19_3 [1, -5, 4] = true := by decide +kernel
theorem subd19_3_980 : subd19_3 [1, -5, 5] = true := by decide +kernel
theorem subd19_3_981 : subd19_3 [1, -5, 6] = true := by decide +kernel
theorem subd19_3_982 : subd19_3 [1, -5, 7] = true := by decide +kernel
theorem subd19_3_983 : subd19_3 [1, -5, 8] = true := by decide +kernel
theorem subd19_3_984 : subd19_3 [1, -4, -7] = true := by decide +kernel
theorem subd19_3_985 : subd19_3 [1, -4, -6] = true := by decide +kernel
theorem subd19_3_986 : subd19_3 [1, -4, -5] = true := by decide +kernel
theorem subd19_3_987 : subd19_3 [1, -4, -4] = true := by decide +kernel
theorem subd19_3_988 : subd19_3 [1, -4, -3] = true := by decide +kernel
theorem subd19_3_989 : subd19_3 [1, -4, -2] = true := by decide +kernel
theorem subd19_3_990 : subd19_3 [1, -4, -1] = true := by decide +kernel
theorem subd19_3_991 : subd19_3 [1, -4, 0] = true := by decide +kernel
theorem sbd19_3_30 : ∀ q ∈ blkd19_3_30, subd19_3 q = true := by
  unfold blkd19_3_30
  exact List.forall_mem_cons.2 ⟨subd19_3_960, List.forall_mem_cons.2 ⟨subd19_3_961, List.forall_mem_cons.2 ⟨subd19_3_962, List.forall_mem_cons.2 ⟨subd19_3_963, List.forall_mem_cons.2 ⟨subd19_3_964, List.forall_mem_cons.2 ⟨subd19_3_965, List.forall_mem_cons.2 ⟨subd19_3_966, List.forall_mem_cons.2 ⟨subd19_3_967, List.forall_mem_cons.2 ⟨subd19_3_968, List.forall_mem_cons.2 ⟨subd19_3_969, List.forall_mem_cons.2 ⟨subd19_3_970, List.forall_mem_cons.2 ⟨subd19_3_971, List.forall_mem_cons.2 ⟨subd19_3_972, List.forall_mem_cons.2 ⟨subd19_3_973, List.forall_mem_cons.2 ⟨subd19_3_974, List.forall_mem_cons.2 ⟨subd19_3_975, List.forall_mem_cons.2 ⟨subd19_3_976, List.forall_mem_cons.2 ⟨subd19_3_977, List.forall_mem_cons.2 ⟨subd19_3_978, List.forall_mem_cons.2 ⟨subd19_3_979, List.forall_mem_cons.2 ⟨subd19_3_980, List.forall_mem_cons.2 ⟨subd19_3_981, List.forall_mem_cons.2 ⟨subd19_3_982, List.forall_mem_cons.2 ⟨subd19_3_983, List.forall_mem_cons.2 ⟨subd19_3_984, List.forall_mem_cons.2 ⟨subd19_3_985, List.forall_mem_cons.2 ⟨subd19_3_986, List.forall_mem_cons.2 ⟨subd19_3_987, List.forall_mem_cons.2 ⟨subd19_3_988, List.forall_mem_cons.2 ⟨subd19_3_989, List.forall_mem_cons.2 ⟨subd19_3_990, List.forall_mem_cons.2 ⟨subd19_3_991, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_3_992 : subd19_3 [1, -4, 1] = true := by decide +kernel
theorem subd19_3_993 : subd19_3 [1, -4, 2] = true := by decide +kernel
theorem subd19_3_994 : subd19_3 [1, -4, 3] = true := by decide +kernel
theorem subd19_3_995 : subd19_3 [1, -4, 4] = true := by decide +kernel
theorem subd19_3_996 : subd19_3 [1, -4, 5] = true := by decide +kernel
theorem subd19_3_997 : subd19_3 [1, -4, 6] = true := by decide +kernel
theorem subd19_3_998 : subd19_3 [1, -4, 7] = true := by decide +kernel
theorem subd19_3_999 : subd19_3 [1, -4, 8] = true := by decide +kernel
theorem subd19_3_1000 : subd19_3 [1, -4, 9] = true := by decide +kernel
theorem subd19_3_1001 : subd19_3 [1, -3, -8] = true := by decide +kernel
theorem subd19_3_1002 : subd19_3 [1, -3, -7] = true := by decide +kernel
theorem subd19_3_1003 : subd19_3 [1, -3, -6] = true := by decide +kernel
theorem subd19_3_1004 : subd19_3 [1, -3, -5] = true := by decide +kernel
theorem subd19_3_1005 : subd19_3 [1, -3, -4] = true := by decide +kernel
theorem subd19_3_1006 : subd19_3 [1, -3, -3] = true := by decide +kernel
theorem subd19_3_1007 : subd19_3 [1, -3, -2] = true := by decide +kernel
theorem subd19_3_1008 : subd19_3 [1, -3, -1] = true := by decide +kernel
theorem subd19_3_1009 : subd19_3 [1, -3, 0] = true := by decide +kernel
theorem subd19_3_1010 : subd19_3 [1, -3, 1] = true := by decide +kernel
theorem subd19_3_1011 : subd19_3 [1, -3, 2] = true := by decide +kernel
theorem subd19_3_1012 : subd19_3 [1, -3, 3] = true := by decide +kernel
theorem subd19_3_1013 : subd19_3 [1, -3, 4] = true := by decide +kernel
theorem subd19_3_1014 : subd19_3 [1, -3, 5] = true := by decide +kernel
theorem subd19_3_1015 : subd19_3 [1, -3, 6] = true := by decide +kernel
theorem subd19_3_1016 : subd19_3 [1, -3, 7] = true := by decide +kernel
theorem subd19_3_1017 : subd19_3 [1, -3, 8] = true := by decide +kernel
theorem subd19_3_1018 : subd19_3 [1, -3, 9] = true := by decide +kernel
theorem subd19_3_1019 : subd19_3 [1, -2, -8] = true := by decide +kernel
theorem subd19_3_1020 : subd19_3 [1, -2, -7] = true := by decide +kernel
theorem subd19_3_1021 : subd19_3 [1, -2, -6] = true := by decide +kernel
theorem subd19_3_1022 : subd19_3 [1, -2, -5] = true := by decide +kernel
theorem subd19_3_1023 : subd19_3 [1, -2, -4] = true := by decide +kernel
theorem sbd19_3_31 : ∀ q ∈ blkd19_3_31, subd19_3 q = true := by
  unfold blkd19_3_31
  exact List.forall_mem_cons.2 ⟨subd19_3_992, List.forall_mem_cons.2 ⟨subd19_3_993, List.forall_mem_cons.2 ⟨subd19_3_994, List.forall_mem_cons.2 ⟨subd19_3_995, List.forall_mem_cons.2 ⟨subd19_3_996, List.forall_mem_cons.2 ⟨subd19_3_997, List.forall_mem_cons.2 ⟨subd19_3_998, List.forall_mem_cons.2 ⟨subd19_3_999, List.forall_mem_cons.2 ⟨subd19_3_1000, List.forall_mem_cons.2 ⟨subd19_3_1001, List.forall_mem_cons.2 ⟨subd19_3_1002, List.forall_mem_cons.2 ⟨subd19_3_1003, List.forall_mem_cons.2 ⟨subd19_3_1004, List.forall_mem_cons.2 ⟨subd19_3_1005, List.forall_mem_cons.2 ⟨subd19_3_1006, List.forall_mem_cons.2 ⟨subd19_3_1007, List.forall_mem_cons.2 ⟨subd19_3_1008, List.forall_mem_cons.2 ⟨subd19_3_1009, List.forall_mem_cons.2 ⟨subd19_3_1010, List.forall_mem_cons.2 ⟨subd19_3_1011, List.forall_mem_cons.2 ⟨subd19_3_1012, List.forall_mem_cons.2 ⟨subd19_3_1013, List.forall_mem_cons.2 ⟨subd19_3_1014, List.forall_mem_cons.2 ⟨subd19_3_1015, List.forall_mem_cons.2 ⟨subd19_3_1016, List.forall_mem_cons.2 ⟨subd19_3_1017, List.forall_mem_cons.2 ⟨subd19_3_1018, List.forall_mem_cons.2 ⟨subd19_3_1019, List.forall_mem_cons.2 ⟨subd19_3_1020, List.forall_mem_cons.2 ⟨subd19_3_1021, List.forall_mem_cons.2 ⟨subd19_3_1022, List.forall_mem_cons.2 ⟨subd19_3_1023, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_3_1024 : subd19_3 [1, -2, -3] = true := by decide +kernel
theorem subd19_3_1025 : subd19_3 [1, -2, -2] = true := by decide +kernel
theorem subd19_3_1026 : subd19_3 [1, -2, -1] = true := by decide +kernel
theorem subd19_3_1027 : subd19_3 [1, -2, 0] = true := by decide +kernel
theorem subd19_3_1028 : subd19_3 [1, -2, 1] = true := by decide +kernel
theorem subd19_3_1029 : subd19_3 [1, -2, 2] = true := by decide +kernel
theorem subd19_3_1030 : subd19_3 [1, -2, 3] = true := by decide +kernel
theorem subd19_3_1031 : subd19_3 [1, -2, 4] = true := by decide +kernel
theorem subd19_3_1032 : subd19_3 [1, -2, 5] = true := by decide +kernel
theorem subd19_3_1033 : subd19_3 [1, -2, 6] = true := by decide +kernel
theorem subd19_3_1034 : subd19_3 [1, -2, 7] = true := by decide +kernel
theorem subd19_3_1035 : subd19_3 [1, -2, 8] = true := by decide +kernel
theorem subd19_3_1036 : subd19_3 [1, -2, 9] = true := by decide +kernel
theorem subd19_3_1037 : subd19_3 [1, -1, -9] = true := by decide +kernel
theorem subd19_3_1038 : subd19_3 [1, -1, -8] = true := by decide +kernel
theorem subd19_3_1039 : subd19_3 [1, -1, -7] = true := by decide +kernel
theorem subd19_3_1040 : subd19_3 [1, -1, -6] = true := by decide +kernel
theorem subd19_3_1041 : subd19_3 [1, -1, -5] = true := by decide +kernel
theorem subd19_3_1042 : subd19_3 [1, -1, -4] = true := by decide +kernel
theorem subd19_3_1043 : subd19_3 [1, -1, -3] = true := by decide +kernel
theorem subd19_3_1044 : subd19_3 [1, -1, -2] = true := by decide +kernel
theorem subd19_3_1045 : subd19_3 [1, -1, -1] = true := by decide +kernel
theorem subd19_3_1046 : subd19_3 [1, -1, 0] = true := by decide +kernel
theorem subd19_3_1047 : subd19_3 [1, -1, 1] = true := by decide +kernel
theorem subd19_3_1048 : subd19_3 [1, -1, 2] = true := by decide +kernel
theorem subd19_3_1049 : subd19_3 [1, -1, 3] = true := by decide +kernel
theorem subd19_3_1050 : subd19_3 [1, -1, 4] = true := by decide +kernel
theorem subd19_3_1051 : subd19_3 [1, -1, 5] = true := by decide +kernel
theorem subd19_3_1052 : subd19_3 [1, -1, 6] = true := by decide +kernel
theorem subd19_3_1053 : subd19_3 [1, -1, 7] = true := by decide +kernel
theorem subd19_3_1054 : subd19_3 [1, -1, 8] = true := by decide +kernel
theorem subd19_3_1055 : subd19_3 [1, 0, -10] = true := by decide +kernel
theorem sbd19_3_32 : ∀ q ∈ blkd19_3_32, subd19_3 q = true := by
  unfold blkd19_3_32
  exact List.forall_mem_cons.2 ⟨subd19_3_1024, List.forall_mem_cons.2 ⟨subd19_3_1025, List.forall_mem_cons.2 ⟨subd19_3_1026, List.forall_mem_cons.2 ⟨subd19_3_1027, List.forall_mem_cons.2 ⟨subd19_3_1028, List.forall_mem_cons.2 ⟨subd19_3_1029, List.forall_mem_cons.2 ⟨subd19_3_1030, List.forall_mem_cons.2 ⟨subd19_3_1031, List.forall_mem_cons.2 ⟨subd19_3_1032, List.forall_mem_cons.2 ⟨subd19_3_1033, List.forall_mem_cons.2 ⟨subd19_3_1034, List.forall_mem_cons.2 ⟨subd19_3_1035, List.forall_mem_cons.2 ⟨subd19_3_1036, List.forall_mem_cons.2 ⟨subd19_3_1037, List.forall_mem_cons.2 ⟨subd19_3_1038, List.forall_mem_cons.2 ⟨subd19_3_1039, List.forall_mem_cons.2 ⟨subd19_3_1040, List.forall_mem_cons.2 ⟨subd19_3_1041, List.forall_mem_cons.2 ⟨subd19_3_1042, List.forall_mem_cons.2 ⟨subd19_3_1043, List.forall_mem_cons.2 ⟨subd19_3_1044, List.forall_mem_cons.2 ⟨subd19_3_1045, List.forall_mem_cons.2 ⟨subd19_3_1046, List.forall_mem_cons.2 ⟨subd19_3_1047, List.forall_mem_cons.2 ⟨subd19_3_1048, List.forall_mem_cons.2 ⟨subd19_3_1049, List.forall_mem_cons.2 ⟨subd19_3_1050, List.forall_mem_cons.2 ⟨subd19_3_1051, List.forall_mem_cons.2 ⟨subd19_3_1052, List.forall_mem_cons.2 ⟨subd19_3_1053, List.forall_mem_cons.2 ⟨subd19_3_1054, List.forall_mem_cons.2 ⟨subd19_3_1055, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_3_1056 : subd19_3 [1, 0, -9] = true := by decide +kernel
theorem subd19_3_1057 : subd19_3 [1, 0, -8] = true := by decide +kernel
theorem subd19_3_1058 : subd19_3 [1, 0, -7] = true := by decide +kernel
theorem subd19_3_1059 : subd19_3 [1, 0, -6] = true := by decide +kernel
theorem subd19_3_1060 : subd19_3 [1, 0, -5] = true := by decide +kernel
theorem subd19_3_1061 : subd19_3 [1, 0, -4] = true := by decide +kernel
theorem subd19_3_1062 : subd19_3 [1, 0, -3] = true := by decide +kernel
theorem subd19_3_1063 : subd19_3 [1, 0, -2] = true := by decide +kernel
theorem subd19_3_1064 : subd19_3 [1, 0, -1] = true := by decide +kernel
theorem subd19_3_1065 : subd19_3 [1, 0, 0] = true := by decide +kernel
theorem subd19_3_1066 : subd19_3 [1, 0, 1] = true := by decide +kernel
theorem subd19_3_1067 : subd19_3 [1, 0, 2] = true := by decide +kernel
theorem subd19_3_1068 : subd19_3 [1, 0, 3] = true := by decide +kernel
theorem subd19_3_1069 : subd19_3 [1, 0, 4] = true := by decide +kernel
theorem subd19_3_1070 : subd19_3 [1, 0, 5] = true := by decide +kernel
theorem subd19_3_1071 : subd19_3 [1, 0, 6] = true := by decide +kernel
theorem subd19_3_1072 : subd19_3 [1, 0, 7] = true := by decide +kernel
theorem subd19_3_1073 : subd19_3 [1, 0, 8] = true := by decide +kernel
theorem subd19_3_1074 : subd19_3 [1, 1, -10] = true := by decide +kernel
theorem subd19_3_1075 : subd19_3 [1, 1, -9] = true := by decide +kernel
theorem subd19_3_1076 : subd19_3 [1, 1, -8] = true := by decide +kernel
theorem subd19_3_1077 : subd19_3 [1, 1, -7] = true := by decide +kernel
theorem subd19_3_1078 : subd19_3 [1, 1, -6] = true := by decide +kernel
theorem subd19_3_1079 : subd19_3 [1, 1, -5] = true := by decide +kernel
theorem subd19_3_1080 : subd19_3 [1, 1, -4] = true := by decide +kernel
theorem subd19_3_1081 : subd19_3 [1, 1, -3] = true := by decide +kernel
theorem subd19_3_1082 : subd19_3 [1, 1, -2] = true := by decide +kernel
theorem subd19_3_1083 : subd19_3 [1, 1, -1] = true := by decide +kernel
theorem subd19_3_1084 : subd19_3 [1, 1, 0] = true := by decide +kernel
theorem subd19_3_1085 : subd19_3 [1, 1, 1] = true := by decide +kernel
theorem subd19_3_1086 : subd19_3 [1, 1, 2] = true := by decide +kernel
theorem subd19_3_1087 : subd19_3 [1, 1, 3] = true := by decide +kernel
theorem sbd19_3_33 : ∀ q ∈ blkd19_3_33, subd19_3 q = true := by
  unfold blkd19_3_33
  exact List.forall_mem_cons.2 ⟨subd19_3_1056, List.forall_mem_cons.2 ⟨subd19_3_1057, List.forall_mem_cons.2 ⟨subd19_3_1058, List.forall_mem_cons.2 ⟨subd19_3_1059, List.forall_mem_cons.2 ⟨subd19_3_1060, List.forall_mem_cons.2 ⟨subd19_3_1061, List.forall_mem_cons.2 ⟨subd19_3_1062, List.forall_mem_cons.2 ⟨subd19_3_1063, List.forall_mem_cons.2 ⟨subd19_3_1064, List.forall_mem_cons.2 ⟨subd19_3_1065, List.forall_mem_cons.2 ⟨subd19_3_1066, List.forall_mem_cons.2 ⟨subd19_3_1067, List.forall_mem_cons.2 ⟨subd19_3_1068, List.forall_mem_cons.2 ⟨subd19_3_1069, List.forall_mem_cons.2 ⟨subd19_3_1070, List.forall_mem_cons.2 ⟨subd19_3_1071, List.forall_mem_cons.2 ⟨subd19_3_1072, List.forall_mem_cons.2 ⟨subd19_3_1073, List.forall_mem_cons.2 ⟨subd19_3_1074, List.forall_mem_cons.2 ⟨subd19_3_1075, List.forall_mem_cons.2 ⟨subd19_3_1076, List.forall_mem_cons.2 ⟨subd19_3_1077, List.forall_mem_cons.2 ⟨subd19_3_1078, List.forall_mem_cons.2 ⟨subd19_3_1079, List.forall_mem_cons.2 ⟨subd19_3_1080, List.forall_mem_cons.2 ⟨subd19_3_1081, List.forall_mem_cons.2 ⟨subd19_3_1082, List.forall_mem_cons.2 ⟨subd19_3_1083, List.forall_mem_cons.2 ⟨subd19_3_1084, List.forall_mem_cons.2 ⟨subd19_3_1085, List.forall_mem_cons.2 ⟨subd19_3_1086, List.forall_mem_cons.2 ⟨subd19_3_1087, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_3_1088 : subd19_3 [1, 1, 4] = true := by decide +kernel
theorem subd19_3_1089 : subd19_3 [1, 1, 5] = true := by decide +kernel
theorem subd19_3_1090 : subd19_3 [1, 1, 6] = true := by decide +kernel
theorem subd19_3_1091 : subd19_3 [1, 1, 7] = true := by decide +kernel
theorem subd19_3_1092 : subd19_3 [1, 2, -10] = true := by decide +kernel
theorem subd19_3_1093 : subd19_3 [1, 2, -9] = true := by decide +kernel
theorem subd19_3_1094 : subd19_3 [1, 2, -8] = true := by decide +kernel
theorem subd19_3_1095 : subd19_3 [1, 2, -7] = true := by decide +kernel
theorem subd19_3_1096 : subd19_3 [1, 2, -6] = true := by decide +kernel
theorem subd19_3_1097 : subd19_3 [1, 2, -5] = true := by decide +kernel
theorem subd19_3_1098 : subd19_3 [1, 2, -4] = true := by decide +kernel
theorem subd19_3_1099 : subd19_3 [1, 2, -3] = true := by decide +kernel
theorem subd19_3_1100 : subd19_3 [1, 2, -2] = true := by decide +kernel
theorem subd19_3_1101 : subd19_3 [1, 2, -1] = true := by decide +kernel
theorem subd19_3_1102 : subd19_3 [1, 2, 0] = true := by decide +kernel
theorem subd19_3_1103 : subd19_3 [1, 2, 1] = true := by decide +kernel
theorem subd19_3_1104 : subd19_3 [1, 2, 2] = true := by decide +kernel
theorem subd19_3_1105 : subd19_3 [1, 2, 3] = true := by decide +kernel
theorem subd19_3_1106 : subd19_3 [1, 2, 4] = true := by decide +kernel
theorem subd19_3_1107 : subd19_3 [1, 2, 5] = true := by decide +kernel
theorem subd19_3_1108 : subd19_3 [1, 2, 6] = true := by decide +kernel
theorem subd19_3_1109 : subd19_3 [1, 2, 7] = true := by decide +kernel
theorem subd19_3_1110 : subd19_3 [1, 3, -10] = true := by decide +kernel
theorem subd19_3_1111 : subd19_3 [1, 3, -9] = true := by decide +kernel
theorem subd19_3_1112 : subd19_3 [1, 3, -8] = true := by decide +kernel
theorem subd19_3_1113 : subd19_3 [1, 3, -7] = true := by decide +kernel
theorem subd19_3_1114 : subd19_3 [1, 3, -6] = true := by decide +kernel
theorem subd19_3_1115 : subd19_3 [1, 3, -5] = true := by decide +kernel
theorem subd19_3_1116 : subd19_3 [1, 3, -4] = true := by decide +kernel
theorem subd19_3_1117 : subd19_3 [1, 3, -3] = true := by decide +kernel
theorem subd19_3_1118 : subd19_3 [1, 3, -2] = true := by decide +kernel
theorem subd19_3_1119 : subd19_3 [1, 3, -1] = true := by decide +kernel
theorem sbd19_3_34 : ∀ q ∈ blkd19_3_34, subd19_3 q = true := by
  unfold blkd19_3_34
  exact List.forall_mem_cons.2 ⟨subd19_3_1088, List.forall_mem_cons.2 ⟨subd19_3_1089, List.forall_mem_cons.2 ⟨subd19_3_1090, List.forall_mem_cons.2 ⟨subd19_3_1091, List.forall_mem_cons.2 ⟨subd19_3_1092, List.forall_mem_cons.2 ⟨subd19_3_1093, List.forall_mem_cons.2 ⟨subd19_3_1094, List.forall_mem_cons.2 ⟨subd19_3_1095, List.forall_mem_cons.2 ⟨subd19_3_1096, List.forall_mem_cons.2 ⟨subd19_3_1097, List.forall_mem_cons.2 ⟨subd19_3_1098, List.forall_mem_cons.2 ⟨subd19_3_1099, List.forall_mem_cons.2 ⟨subd19_3_1100, List.forall_mem_cons.2 ⟨subd19_3_1101, List.forall_mem_cons.2 ⟨subd19_3_1102, List.forall_mem_cons.2 ⟨subd19_3_1103, List.forall_mem_cons.2 ⟨subd19_3_1104, List.forall_mem_cons.2 ⟨subd19_3_1105, List.forall_mem_cons.2 ⟨subd19_3_1106, List.forall_mem_cons.2 ⟨subd19_3_1107, List.forall_mem_cons.2 ⟨subd19_3_1108, List.forall_mem_cons.2 ⟨subd19_3_1109, List.forall_mem_cons.2 ⟨subd19_3_1110, List.forall_mem_cons.2 ⟨subd19_3_1111, List.forall_mem_cons.2 ⟨subd19_3_1112, List.forall_mem_cons.2 ⟨subd19_3_1113, List.forall_mem_cons.2 ⟨subd19_3_1114, List.forall_mem_cons.2 ⟨subd19_3_1115, List.forall_mem_cons.2 ⟨subd19_3_1116, List.forall_mem_cons.2 ⟨subd19_3_1117, List.forall_mem_cons.2 ⟨subd19_3_1118, List.forall_mem_cons.2 ⟨subd19_3_1119, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_3_1120 : subd19_3 [1, 3, 0] = true := by decide +kernel
theorem subd19_3_1121 : subd19_3 [1, 3, 1] = true := by decide +kernel
theorem subd19_3_1122 : subd19_3 [1, 3, 2] = true := by decide +kernel
theorem subd19_3_1123 : subd19_3 [1, 3, 3] = true := by decide +kernel
theorem subd19_3_1124 : subd19_3 [1, 3, 4] = true := by decide +kernel
theorem subd19_3_1125 : subd19_3 [1, 3, 5] = true := by decide +kernel
theorem subd19_3_1126 : subd19_3 [1, 3, 6] = true := by decide +kernel
theorem subd19_3_1127 : subd19_3 [1, 4, -10] = true := by decide +kernel
theorem subd19_3_1128 : subd19_3 [1, 4, -9] = true := by decide +kernel
theorem subd19_3_1129 : subd19_3 [1, 4, -8] = true := by decide +kernel
theorem subd19_3_1130 : subd19_3 [1, 4, -7] = true := by decide +kernel
theorem subd19_3_1131 : subd19_3 [1, 4, -6] = true := by decide +kernel
theorem subd19_3_1132 : subd19_3 [1, 4, -5] = true := by decide +kernel
theorem subd19_3_1133 : subd19_3 [1, 4, -4] = true := by decide +kernel
theorem subd19_3_1134 : subd19_3 [1, 4, -3] = true := by decide +kernel
theorem subd19_3_1135 : subd19_3 [1, 4, -2] = true := by decide +kernel
theorem subd19_3_1136 : subd19_3 [1, 4, -1] = true := by decide +kernel
theorem subd19_3_1137 : subd19_3 [1, 4, 0] = true := by decide +kernel
theorem subd19_3_1138 : subd19_3 [1, 4, 1] = true := by decide +kernel
theorem subd19_3_1139 : subd19_3 [1, 4, 2] = true := by decide +kernel
theorem subd19_3_1140 : subd19_3 [1, 4, 3] = true := by decide +kernel
theorem subd19_3_1141 : subd19_3 [1, 4, 4] = true := by decide +kernel
theorem subd19_3_1142 : subd19_3 [1, 4, 5] = true := by decide +kernel
theorem subd19_3_1143 : subd19_3 [1, 5, -10] = true := by decide +kernel
theorem subd19_3_1144 : subd19_3 [1, 5, -9] = true := by decide +kernel
theorem subd19_3_1145 : subd19_3 [1, 5, -8] = true := by decide +kernel
theorem subd19_3_1146 : subd19_3 [1, 5, -7] = true := by decide +kernel
theorem subd19_3_1147 : subd19_3 [1, 5, -6] = true := by decide +kernel
theorem subd19_3_1148 : subd19_3 [1, 5, -5] = true := by decide +kernel
theorem subd19_3_1149 : subd19_3 [1, 5, -4] = true := by decide +kernel
theorem subd19_3_1150 : subd19_3 [1, 5, -3] = true := by decide +kernel
theorem subd19_3_1151 : subd19_3 [1, 5, -2] = true := by decide +kernel
theorem sbd19_3_35 : ∀ q ∈ blkd19_3_35, subd19_3 q = true := by
  unfold blkd19_3_35
  exact List.forall_mem_cons.2 ⟨subd19_3_1120, List.forall_mem_cons.2 ⟨subd19_3_1121, List.forall_mem_cons.2 ⟨subd19_3_1122, List.forall_mem_cons.2 ⟨subd19_3_1123, List.forall_mem_cons.2 ⟨subd19_3_1124, List.forall_mem_cons.2 ⟨subd19_3_1125, List.forall_mem_cons.2 ⟨subd19_3_1126, List.forall_mem_cons.2 ⟨subd19_3_1127, List.forall_mem_cons.2 ⟨subd19_3_1128, List.forall_mem_cons.2 ⟨subd19_3_1129, List.forall_mem_cons.2 ⟨subd19_3_1130, List.forall_mem_cons.2 ⟨subd19_3_1131, List.forall_mem_cons.2 ⟨subd19_3_1132, List.forall_mem_cons.2 ⟨subd19_3_1133, List.forall_mem_cons.2 ⟨subd19_3_1134, List.forall_mem_cons.2 ⟨subd19_3_1135, List.forall_mem_cons.2 ⟨subd19_3_1136, List.forall_mem_cons.2 ⟨subd19_3_1137, List.forall_mem_cons.2 ⟨subd19_3_1138, List.forall_mem_cons.2 ⟨subd19_3_1139, List.forall_mem_cons.2 ⟨subd19_3_1140, List.forall_mem_cons.2 ⟨subd19_3_1141, List.forall_mem_cons.2 ⟨subd19_3_1142, List.forall_mem_cons.2 ⟨subd19_3_1143, List.forall_mem_cons.2 ⟨subd19_3_1144, List.forall_mem_cons.2 ⟨subd19_3_1145, List.forall_mem_cons.2 ⟨subd19_3_1146, List.forall_mem_cons.2 ⟨subd19_3_1147, List.forall_mem_cons.2 ⟨subd19_3_1148, List.forall_mem_cons.2 ⟨subd19_3_1149, List.forall_mem_cons.2 ⟨subd19_3_1150, List.forall_mem_cons.2 ⟨subd19_3_1151, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_3_1152 : subd19_3 [1, 5, -1] = true := by decide +kernel
theorem subd19_3_1153 : subd19_3 [1, 5, 0] = true := by decide +kernel
theorem subd19_3_1154 : subd19_3 [1, 5, 1] = true := by decide +kernel
theorem subd19_3_1155 : subd19_3 [1, 5, 2] = true := by decide +kernel
theorem subd19_3_1156 : subd19_3 [1, 5, 3] = true := by decide +kernel
theorem subd19_3_1157 : subd19_3 [1, 5, 4] = true := by decide +kernel
theorem subd19_3_1158 : subd19_3 [1, 6] = true := by decide +kernel
theorem subd19_3_1159 : subd19_3 [1, 7] = true := by decide +kernel
theorem subd19_3_1160 : subd19_3 [2, -8] = true := by decide +kernel
theorem subd19_3_1161 : subd19_3 [2, -7] = true := by decide +kernel
theorem subd19_3_1162 : subd19_3 [2, -6] = true := by decide +kernel
theorem subd19_3_1163 : subd19_3 [2, -5, -6] = true := by decide +kernel
theorem subd19_3_1164 : subd19_3 [2, -5, -5] = true := by decide +kernel
theorem subd19_3_1165 : subd19_3 [2, -5, -4] = true := by decide +kernel
theorem subd19_3_1166 : subd19_3 [2, -5, -3] = true := by decide +kernel
theorem subd19_3_1167 : subd19_3 [2, -5, -2] = true := by decide +kernel
theorem subd19_3_1168 : subd19_3 [2, -5, -1] = true := by decide +kernel
theorem subd19_3_1169 : subd19_3 [2, -5, 0] = true := by decide +kernel
theorem subd19_3_1170 : subd19_3 [2, -5, 1] = true := by decide +kernel
theorem subd19_3_1171 : subd19_3 [2, -5, 2] = true := by decide +kernel
theorem subd19_3_1172 : subd19_3 [2, -5, 3] = true := by decide +kernel
theorem subd19_3_1173 : subd19_3 [2, -5, 4] = true := by decide +kernel
theorem subd19_3_1174 : subd19_3 [2, -5, 5] = true := by decide +kernel
theorem subd19_3_1175 : subd19_3 [2, -5, 6] = true := by decide +kernel
theorem subd19_3_1176 : subd19_3 [2, -5, 7] = true := by decide +kernel
theorem subd19_3_1177 : subd19_3 [2, -5, 8] = true := by decide +kernel
theorem subd19_3_1178 : subd19_3 [2, -4, -7] = true := by decide +kernel
theorem subd19_3_1179 : subd19_3 [2, -4, -6] = true := by decide +kernel
theorem subd19_3_1180 : subd19_3 [2, -4, -5] = true := by decide +kernel
theorem subd19_3_1181 : subd19_3 [2, -4, -4] = true := by decide +kernel
theorem subd19_3_1182 : subd19_3 [2, -4, -3] = true := by decide +kernel
theorem subd19_3_1183 : subd19_3 [2, -4, -2] = true := by decide +kernel
theorem sbd19_3_36 : ∀ q ∈ blkd19_3_36, subd19_3 q = true := by
  unfold blkd19_3_36
  exact List.forall_mem_cons.2 ⟨subd19_3_1152, List.forall_mem_cons.2 ⟨subd19_3_1153, List.forall_mem_cons.2 ⟨subd19_3_1154, List.forall_mem_cons.2 ⟨subd19_3_1155, List.forall_mem_cons.2 ⟨subd19_3_1156, List.forall_mem_cons.2 ⟨subd19_3_1157, List.forall_mem_cons.2 ⟨subd19_3_1158, List.forall_mem_cons.2 ⟨subd19_3_1159, List.forall_mem_cons.2 ⟨subd19_3_1160, List.forall_mem_cons.2 ⟨subd19_3_1161, List.forall_mem_cons.2 ⟨subd19_3_1162, List.forall_mem_cons.2 ⟨subd19_3_1163, List.forall_mem_cons.2 ⟨subd19_3_1164, List.forall_mem_cons.2 ⟨subd19_3_1165, List.forall_mem_cons.2 ⟨subd19_3_1166, List.forall_mem_cons.2 ⟨subd19_3_1167, List.forall_mem_cons.2 ⟨subd19_3_1168, List.forall_mem_cons.2 ⟨subd19_3_1169, List.forall_mem_cons.2 ⟨subd19_3_1170, List.forall_mem_cons.2 ⟨subd19_3_1171, List.forall_mem_cons.2 ⟨subd19_3_1172, List.forall_mem_cons.2 ⟨subd19_3_1173, List.forall_mem_cons.2 ⟨subd19_3_1174, List.forall_mem_cons.2 ⟨subd19_3_1175, List.forall_mem_cons.2 ⟨subd19_3_1176, List.forall_mem_cons.2 ⟨subd19_3_1177, List.forall_mem_cons.2 ⟨subd19_3_1178, List.forall_mem_cons.2 ⟨subd19_3_1179, List.forall_mem_cons.2 ⟨subd19_3_1180, List.forall_mem_cons.2 ⟨subd19_3_1181, List.forall_mem_cons.2 ⟨subd19_3_1182, List.forall_mem_cons.2 ⟨subd19_3_1183, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_3_1184 : subd19_3 [2, -4, -1] = true := by decide +kernel
theorem subd19_3_1185 : subd19_3 [2, -4, 0] = true := by decide +kernel
theorem subd19_3_1186 : subd19_3 [2, -4, 1] = true := by decide +kernel
theorem subd19_3_1187 : subd19_3 [2, -4, 2] = true := by decide +kernel
theorem subd19_3_1188 : subd19_3 [2, -4, 3] = true := by decide +kernel
theorem subd19_3_1189 : subd19_3 [2, -4, 4] = true := by decide +kernel
theorem subd19_3_1190 : subd19_3 [2, -4, 5] = true := by decide +kernel
theorem subd19_3_1191 : subd19_3 [2, -4, 6] = true := by decide +kernel
theorem subd19_3_1192 : subd19_3 [2, -4, 7] = true := by decide +kernel
theorem subd19_3_1193 : subd19_3 [2, -4, 8] = true := by decide +kernel
theorem subd19_3_1194 : subd19_3 [2, -3, -8] = true := by decide +kernel
theorem subd19_3_1195 : subd19_3 [2, -3, -7] = true := by decide +kernel
theorem subd19_3_1196 : subd19_3 [2, -3, -6] = true := by decide +kernel
theorem subd19_3_1197 : subd19_3 [2, -3, -5] = true := by decide +kernel
theorem subd19_3_1198 : subd19_3 [2, -3, -4] = true := by decide +kernel
theorem subd19_3_1199 : subd19_3 [2, -3, -3] = true := by decide +kernel
theorem subd19_3_1200 : subd19_3 [2, -3, -2] = true := by decide +kernel
theorem subd19_3_1201 : subd19_3 [2, -3, -1] = true := by decide +kernel
theorem subd19_3_1202 : subd19_3 [2, -3, 0] = true := by decide +kernel
theorem subd19_3_1203 : subd19_3 [2, -3, 1] = true := by decide +kernel
theorem subd19_3_1204 : subd19_3 [2, -3, 2] = true := by decide +kernel
theorem subd19_3_1205 : subd19_3 [2, -3, 3] = true := by decide +kernel
theorem subd19_3_1206 : subd19_3 [2, -3, 4] = true := by decide +kernel
theorem subd19_3_1207 : subd19_3 [2, -3, 5] = true := by decide +kernel
theorem subd19_3_1208 : subd19_3 [2, -3, 6] = true := by decide +kernel
theorem subd19_3_1209 : subd19_3 [2, -3, 7] = true := by decide +kernel
theorem subd19_3_1210 : subd19_3 [2, -3, 8] = true := by decide +kernel
theorem subd19_3_1211 : subd19_3 [2, -2, -9] = true := by decide +kernel
theorem subd19_3_1212 : subd19_3 [2, -2, -8] = true := by decide +kernel
theorem subd19_3_1213 : subd19_3 [2, -2, -7] = true := by decide +kernel
theorem subd19_3_1214 : subd19_3 [2, -2, -6] = true := by decide +kernel
theorem subd19_3_1215 : subd19_3 [2, -2, -5] = true := by decide +kernel
theorem sbd19_3_37 : ∀ q ∈ blkd19_3_37, subd19_3 q = true := by
  unfold blkd19_3_37
  exact List.forall_mem_cons.2 ⟨subd19_3_1184, List.forall_mem_cons.2 ⟨subd19_3_1185, List.forall_mem_cons.2 ⟨subd19_3_1186, List.forall_mem_cons.2 ⟨subd19_3_1187, List.forall_mem_cons.2 ⟨subd19_3_1188, List.forall_mem_cons.2 ⟨subd19_3_1189, List.forall_mem_cons.2 ⟨subd19_3_1190, List.forall_mem_cons.2 ⟨subd19_3_1191, List.forall_mem_cons.2 ⟨subd19_3_1192, List.forall_mem_cons.2 ⟨subd19_3_1193, List.forall_mem_cons.2 ⟨subd19_3_1194, List.forall_mem_cons.2 ⟨subd19_3_1195, List.forall_mem_cons.2 ⟨subd19_3_1196, List.forall_mem_cons.2 ⟨subd19_3_1197, List.forall_mem_cons.2 ⟨subd19_3_1198, List.forall_mem_cons.2 ⟨subd19_3_1199, List.forall_mem_cons.2 ⟨subd19_3_1200, List.forall_mem_cons.2 ⟨subd19_3_1201, List.forall_mem_cons.2 ⟨subd19_3_1202, List.forall_mem_cons.2 ⟨subd19_3_1203, List.forall_mem_cons.2 ⟨subd19_3_1204, List.forall_mem_cons.2 ⟨subd19_3_1205, List.forall_mem_cons.2 ⟨subd19_3_1206, List.forall_mem_cons.2 ⟨subd19_3_1207, List.forall_mem_cons.2 ⟨subd19_3_1208, List.forall_mem_cons.2 ⟨subd19_3_1209, List.forall_mem_cons.2 ⟨subd19_3_1210, List.forall_mem_cons.2 ⟨subd19_3_1211, List.forall_mem_cons.2 ⟨subd19_3_1212, List.forall_mem_cons.2 ⟨subd19_3_1213, List.forall_mem_cons.2 ⟨subd19_3_1214, List.forall_mem_cons.2 ⟨subd19_3_1215, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_3_1216 : subd19_3 [2, -2, -4] = true := by decide +kernel
theorem subd19_3_1217 : subd19_3 [2, -2, -3] = true := by decide +kernel
theorem subd19_3_1218 : subd19_3 [2, -2, -2] = true := by decide +kernel
theorem subd19_3_1219 : subd19_3 [2, -2, -1] = true := by decide +kernel
theorem subd19_3_1220 : subd19_3 [2, -2, 0] = true := by decide +kernel
theorem subd19_3_1221 : subd19_3 [2, -2, 1] = true := by decide +kernel
theorem subd19_3_1222 : subd19_3 [2, -2, 2] = true := by decide +kernel
theorem subd19_3_1223 : subd19_3 [2, -2, 3] = true := by decide +kernel
theorem subd19_3_1224 : subd19_3 [2, -2, 4] = true := by decide +kernel
theorem subd19_3_1225 : subd19_3 [2, -2, 5] = true := by decide +kernel
theorem subd19_3_1226 : subd19_3 [2, -2, 6] = true := by decide +kernel
theorem subd19_3_1227 : subd19_3 [2, -2, 7] = true := by decide +kernel
theorem subd19_3_1228 : subd19_3 [2, -2, 8] = true := by decide +kernel
theorem subd19_3_1229 : subd19_3 [2, -1, -9] = true := by decide +kernel
theorem subd19_3_1230 : subd19_3 [2, -1, -8] = true := by decide +kernel
theorem subd19_3_1231 : subd19_3 [2, -1, -7] = true := by decide +kernel
theorem subd19_3_1232 : subd19_3 [2, -1, -6] = true := by decide +kernel
theorem subd19_3_1233 : subd19_3 [2, -1, -5] = true := by decide +kernel
theorem subd19_3_1234 : subd19_3 [2, -1, -4] = true := by decide +kernel
theorem subd19_3_1235 : subd19_3 [2, -1, -3] = true := by decide +kernel
theorem subd19_3_1236 : subd19_3 [2, -1, -2] = true := by decide +kernel
theorem subd19_3_1237 : subd19_3 [2, -1, -1] = true := by decide +kernel
theorem subd19_3_1238 : subd19_3 [2, -1, 0] = true := by decide +kernel
theorem subd19_3_1239 : subd19_3 [2, -1, 1] = true := by decide +kernel
theorem subd19_3_1240 : subd19_3 [2, -1, 2] = true := by decide +kernel
theorem subd19_3_1241 : subd19_3 [2, -1, 3] = true := by decide +kernel
theorem subd19_3_1242 : subd19_3 [2, -1, 4] = true := by decide +kernel
theorem subd19_3_1243 : subd19_3 [2, -1, 5] = true := by decide +kernel
theorem subd19_3_1244 : subd19_3 [2, -1, 6] = true := by decide +kernel
theorem subd19_3_1245 : subd19_3 [2, -1, 7] = true := by decide +kernel
theorem subd19_3_1246 : subd19_3 [2, -1, 8] = true := by decide +kernel
theorem subd19_3_1247 : subd19_3 [2, 0, -10] = true := by decide +kernel
theorem sbd19_3_38 : ∀ q ∈ blkd19_3_38, subd19_3 q = true := by
  unfold blkd19_3_38
  exact List.forall_mem_cons.2 ⟨subd19_3_1216, List.forall_mem_cons.2 ⟨subd19_3_1217, List.forall_mem_cons.2 ⟨subd19_3_1218, List.forall_mem_cons.2 ⟨subd19_3_1219, List.forall_mem_cons.2 ⟨subd19_3_1220, List.forall_mem_cons.2 ⟨subd19_3_1221, List.forall_mem_cons.2 ⟨subd19_3_1222, List.forall_mem_cons.2 ⟨subd19_3_1223, List.forall_mem_cons.2 ⟨subd19_3_1224, List.forall_mem_cons.2 ⟨subd19_3_1225, List.forall_mem_cons.2 ⟨subd19_3_1226, List.forall_mem_cons.2 ⟨subd19_3_1227, List.forall_mem_cons.2 ⟨subd19_3_1228, List.forall_mem_cons.2 ⟨subd19_3_1229, List.forall_mem_cons.2 ⟨subd19_3_1230, List.forall_mem_cons.2 ⟨subd19_3_1231, List.forall_mem_cons.2 ⟨subd19_3_1232, List.forall_mem_cons.2 ⟨subd19_3_1233, List.forall_mem_cons.2 ⟨subd19_3_1234, List.forall_mem_cons.2 ⟨subd19_3_1235, List.forall_mem_cons.2 ⟨subd19_3_1236, List.forall_mem_cons.2 ⟨subd19_3_1237, List.forall_mem_cons.2 ⟨subd19_3_1238, List.forall_mem_cons.2 ⟨subd19_3_1239, List.forall_mem_cons.2 ⟨subd19_3_1240, List.forall_mem_cons.2 ⟨subd19_3_1241, List.forall_mem_cons.2 ⟨subd19_3_1242, List.forall_mem_cons.2 ⟨subd19_3_1243, List.forall_mem_cons.2 ⟨subd19_3_1244, List.forall_mem_cons.2 ⟨subd19_3_1245, List.forall_mem_cons.2 ⟨subd19_3_1246, List.forall_mem_cons.2 ⟨subd19_3_1247, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_3_1248 : subd19_3 [2, 0, -9] = true := by decide +kernel
theorem subd19_3_1249 : subd19_3 [2, 0, -8] = true := by decide +kernel
theorem subd19_3_1250 : subd19_3 [2, 0, -7] = true := by decide +kernel
theorem subd19_3_1251 : subd19_3 [2, 0, -6] = true := by decide +kernel
theorem subd19_3_1252 : subd19_3 [2, 0, -5] = true := by decide +kernel
theorem subd19_3_1253 : subd19_3 [2, 0, -4] = true := by decide +kernel
theorem subd19_3_1254 : subd19_3 [2, 0, -3] = true := by decide +kernel
theorem subd19_3_1255 : subd19_3 [2, 0, -2] = true := by decide +kernel
theorem subd19_3_1256 : subd19_3 [2, 0, -1] = true := by decide +kernel
theorem subd19_3_1257 : subd19_3 [2, 0, 0] = true := by decide +kernel
theorem subd19_3_1258 : subd19_3 [2, 0, 1] = true := by decide +kernel
theorem subd19_3_1259 : subd19_3 [2, 0, 2] = true := by decide +kernel
theorem subd19_3_1260 : subd19_3 [2, 0, 3] = true := by decide +kernel
theorem subd19_3_1261 : subd19_3 [2, 0, 4] = true := by decide +kernel
theorem subd19_3_1262 : subd19_3 [2, 0, 5] = true := by decide +kernel
theorem subd19_3_1263 : subd19_3 [2, 0, 6] = true := by decide +kernel
theorem subd19_3_1264 : subd19_3 [2, 0, 7] = true := by decide +kernel
theorem subd19_3_1265 : subd19_3 [2, 1, -10] = true := by decide +kernel
theorem subd19_3_1266 : subd19_3 [2, 1, -9] = true := by decide +kernel
theorem subd19_3_1267 : subd19_3 [2, 1, -8] = true := by decide +kernel
theorem subd19_3_1268 : subd19_3 [2, 1, -7] = true := by decide +kernel
theorem subd19_3_1269 : subd19_3 [2, 1, -6] = true := by decide +kernel
theorem subd19_3_1270 : subd19_3 [2, 1, -5] = true := by decide +kernel
theorem subd19_3_1271 : subd19_3 [2, 1, -4] = true := by decide +kernel
theorem subd19_3_1272 : subd19_3 [2, 1, -3] = true := by decide +kernel
theorem subd19_3_1273 : subd19_3 [2, 1, -2] = true := by decide +kernel
theorem subd19_3_1274 : subd19_3 [2, 1, -1] = true := by decide +kernel
theorem subd19_3_1275 : subd19_3 [2, 1, 0] = true := by decide +kernel
theorem subd19_3_1276 : subd19_3 [2, 1, 1] = true := by decide +kernel
theorem subd19_3_1277 : subd19_3 [2, 1, 2] = true := by decide +kernel
theorem subd19_3_1278 : subd19_3 [2, 1, 3] = true := by decide +kernel
theorem subd19_3_1279 : subd19_3 [2, 1, 4] = true := by decide +kernel
theorem sbd19_3_39 : ∀ q ∈ blkd19_3_39, subd19_3 q = true := by
  unfold blkd19_3_39
  exact List.forall_mem_cons.2 ⟨subd19_3_1248, List.forall_mem_cons.2 ⟨subd19_3_1249, List.forall_mem_cons.2 ⟨subd19_3_1250, List.forall_mem_cons.2 ⟨subd19_3_1251, List.forall_mem_cons.2 ⟨subd19_3_1252, List.forall_mem_cons.2 ⟨subd19_3_1253, List.forall_mem_cons.2 ⟨subd19_3_1254, List.forall_mem_cons.2 ⟨subd19_3_1255, List.forall_mem_cons.2 ⟨subd19_3_1256, List.forall_mem_cons.2 ⟨subd19_3_1257, List.forall_mem_cons.2 ⟨subd19_3_1258, List.forall_mem_cons.2 ⟨subd19_3_1259, List.forall_mem_cons.2 ⟨subd19_3_1260, List.forall_mem_cons.2 ⟨subd19_3_1261, List.forall_mem_cons.2 ⟨subd19_3_1262, List.forall_mem_cons.2 ⟨subd19_3_1263, List.forall_mem_cons.2 ⟨subd19_3_1264, List.forall_mem_cons.2 ⟨subd19_3_1265, List.forall_mem_cons.2 ⟨subd19_3_1266, List.forall_mem_cons.2 ⟨subd19_3_1267, List.forall_mem_cons.2 ⟨subd19_3_1268, List.forall_mem_cons.2 ⟨subd19_3_1269, List.forall_mem_cons.2 ⟨subd19_3_1270, List.forall_mem_cons.2 ⟨subd19_3_1271, List.forall_mem_cons.2 ⟨subd19_3_1272, List.forall_mem_cons.2 ⟨subd19_3_1273, List.forall_mem_cons.2 ⟨subd19_3_1274, List.forall_mem_cons.2 ⟨subd19_3_1275, List.forall_mem_cons.2 ⟨subd19_3_1276, List.forall_mem_cons.2 ⟨subd19_3_1277, List.forall_mem_cons.2 ⟨subd19_3_1278, List.forall_mem_cons.2 ⟨subd19_3_1279, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_3_1280 : subd19_3 [2, 1, 5] = true := by decide +kernel
theorem subd19_3_1281 : subd19_3 [2, 1, 6] = true := by decide +kernel
theorem subd19_3_1282 : subd19_3 [2, 1, 7] = true := by decide +kernel
theorem subd19_3_1283 : subd19_3 [2, 2, -10] = true := by decide +kernel
theorem subd19_3_1284 : subd19_3 [2, 2, -9] = true := by decide +kernel
theorem subd19_3_1285 : subd19_3 [2, 2, -8] = true := by decide +kernel
theorem subd19_3_1286 : subd19_3 [2, 2, -7] = true := by decide +kernel
theorem subd19_3_1287 : subd19_3 [2, 2, -6] = true := by decide +kernel
theorem subd19_3_1288 : subd19_3 [2, 2, -5] = true := by decide +kernel
theorem subd19_3_1289 : subd19_3 [2, 2, -4] = true := by decide +kernel
theorem subd19_3_1290 : subd19_3 [2, 2, -3] = true := by decide +kernel
theorem subd19_3_1291 : subd19_3 [2, 2, -2] = true := by decide +kernel
theorem subd19_3_1292 : subd19_3 [2, 2, -1] = true := by decide +kernel
theorem subd19_3_1293 : subd19_3 [2, 2, 0] = true := by decide +kernel
theorem subd19_3_1294 : subd19_3 [2, 2, 1] = true := by decide +kernel
theorem subd19_3_1295 : subd19_3 [2, 2, 2] = true := by decide +kernel
theorem subd19_3_1296 : subd19_3 [2, 2, 3] = true := by decide +kernel
theorem subd19_3_1297 : subd19_3 [2, 2, 4] = true := by decide +kernel
theorem subd19_3_1298 : subd19_3 [2, 2, 5] = true := by decide +kernel
theorem subd19_3_1299 : subd19_3 [2, 2, 6] = true := by decide +kernel
theorem subd19_3_1300 : subd19_3 [2, 3, -10] = true := by decide +kernel
theorem subd19_3_1301 : subd19_3 [2, 3, -9] = true := by decide +kernel
theorem subd19_3_1302 : subd19_3 [2, 3, -8] = true := by decide +kernel
theorem subd19_3_1303 : subd19_3 [2, 3, -7] = true := by decide +kernel
theorem subd19_3_1304 : subd19_3 [2, 3, -6] = true := by decide +kernel
theorem subd19_3_1305 : subd19_3 [2, 3, -5] = true := by decide +kernel
theorem subd19_3_1306 : subd19_3 [2, 3, -4] = true := by decide +kernel
theorem subd19_3_1307 : subd19_3 [2, 3, -3] = true := by decide +kernel
theorem subd19_3_1308 : subd19_3 [2, 3, -2] = true := by decide +kernel
theorem subd19_3_1309 : subd19_3 [2, 3, -1] = true := by decide +kernel
theorem subd19_3_1310 : subd19_3 [2, 3, 0] = true := by decide +kernel
theorem subd19_3_1311 : subd19_3 [2, 3, 1] = true := by decide +kernel
theorem sbd19_3_40 : ∀ q ∈ blkd19_3_40, subd19_3 q = true := by
  unfold blkd19_3_40
  exact List.forall_mem_cons.2 ⟨subd19_3_1280, List.forall_mem_cons.2 ⟨subd19_3_1281, List.forall_mem_cons.2 ⟨subd19_3_1282, List.forall_mem_cons.2 ⟨subd19_3_1283, List.forall_mem_cons.2 ⟨subd19_3_1284, List.forall_mem_cons.2 ⟨subd19_3_1285, List.forall_mem_cons.2 ⟨subd19_3_1286, List.forall_mem_cons.2 ⟨subd19_3_1287, List.forall_mem_cons.2 ⟨subd19_3_1288, List.forall_mem_cons.2 ⟨subd19_3_1289, List.forall_mem_cons.2 ⟨subd19_3_1290, List.forall_mem_cons.2 ⟨subd19_3_1291, List.forall_mem_cons.2 ⟨subd19_3_1292, List.forall_mem_cons.2 ⟨subd19_3_1293, List.forall_mem_cons.2 ⟨subd19_3_1294, List.forall_mem_cons.2 ⟨subd19_3_1295, List.forall_mem_cons.2 ⟨subd19_3_1296, List.forall_mem_cons.2 ⟨subd19_3_1297, List.forall_mem_cons.2 ⟨subd19_3_1298, List.forall_mem_cons.2 ⟨subd19_3_1299, List.forall_mem_cons.2 ⟨subd19_3_1300, List.forall_mem_cons.2 ⟨subd19_3_1301, List.forall_mem_cons.2 ⟨subd19_3_1302, List.forall_mem_cons.2 ⟨subd19_3_1303, List.forall_mem_cons.2 ⟨subd19_3_1304, List.forall_mem_cons.2 ⟨subd19_3_1305, List.forall_mem_cons.2 ⟨subd19_3_1306, List.forall_mem_cons.2 ⟨subd19_3_1307, List.forall_mem_cons.2 ⟨subd19_3_1308, List.forall_mem_cons.2 ⟨subd19_3_1309, List.forall_mem_cons.2 ⟨subd19_3_1310, List.forall_mem_cons.2 ⟨subd19_3_1311, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_3_1312 : subd19_3 [2, 3, 2] = true := by decide +kernel
theorem subd19_3_1313 : subd19_3 [2, 3, 3] = true := by decide +kernel
theorem subd19_3_1314 : subd19_3 [2, 3, 4] = true := by decide +kernel
theorem subd19_3_1315 : subd19_3 [2, 3, 5] = true := by decide +kernel
theorem subd19_3_1316 : subd19_3 [2, 4, -10] = true := by decide +kernel
theorem subd19_3_1317 : subd19_3 [2, 4, -9] = true := by decide +kernel
theorem subd19_3_1318 : subd19_3 [2, 4, -8] = true := by decide +kernel
theorem subd19_3_1319 : subd19_3 [2, 4, -7] = true := by decide +kernel
theorem subd19_3_1320 : subd19_3 [2, 4, -6] = true := by decide +kernel
theorem subd19_3_1321 : subd19_3 [2, 4, -5] = true := by decide +kernel
theorem subd19_3_1322 : subd19_3 [2, 4, -4] = true := by decide +kernel
theorem subd19_3_1323 : subd19_3 [2, 4, -3] = true := by decide +kernel
theorem subd19_3_1324 : subd19_3 [2, 4, -2] = true := by decide +kernel
theorem subd19_3_1325 : subd19_3 [2, 4, -1] = true := by decide +kernel
theorem subd19_3_1326 : subd19_3 [2, 4, 0] = true := by decide +kernel
theorem subd19_3_1327 : subd19_3 [2, 4, 1] = true := by decide +kernel
theorem subd19_3_1328 : subd19_3 [2, 4, 2] = true := by decide +kernel
theorem subd19_3_1329 : subd19_3 [2, 4, 3] = true := by decide +kernel
theorem subd19_3_1330 : subd19_3 [2, 4, 4] = true := by decide +kernel
theorem subd19_3_1331 : subd19_3 [2, 5] = true := by decide +kernel
theorem subd19_3_1332 : subd19_3 [2, 6] = true := by decide +kernel
theorem subd19_3_1333 : subd19_3 [2, 7] = true := by decide +kernel
theorem subd19_3_1334 : subd19_3 [3, -8] = true := by decide +kernel
theorem subd19_3_1335 : subd19_3 [3, -7] = true := by decide +kernel
theorem subd19_3_1336 : subd19_3 [3, -6] = true := by decide +kernel
theorem subd19_3_1337 : subd19_3 [3, -5] = true := by decide +kernel
theorem subd19_3_1338 : subd19_3 [3, -4, -7] = true := by decide +kernel
theorem subd19_3_1339 : subd19_3 [3, -4, -6] = true := by decide +kernel
theorem subd19_3_1340 : subd19_3 [3, -4, -5] = true := by decide +kernel
theorem subd19_3_1341 : subd19_3 [3, -4, -4] = true := by decide +kernel
theorem subd19_3_1342 : subd19_3 [3, -4, -3] = true := by decide +kernel
theorem subd19_3_1343 : subd19_3 [3, -4, -2] = true := by decide +kernel
theorem sbd19_3_41 : ∀ q ∈ blkd19_3_41, subd19_3 q = true := by
  unfold blkd19_3_41
  exact List.forall_mem_cons.2 ⟨subd19_3_1312, List.forall_mem_cons.2 ⟨subd19_3_1313, List.forall_mem_cons.2 ⟨subd19_3_1314, List.forall_mem_cons.2 ⟨subd19_3_1315, List.forall_mem_cons.2 ⟨subd19_3_1316, List.forall_mem_cons.2 ⟨subd19_3_1317, List.forall_mem_cons.2 ⟨subd19_3_1318, List.forall_mem_cons.2 ⟨subd19_3_1319, List.forall_mem_cons.2 ⟨subd19_3_1320, List.forall_mem_cons.2 ⟨subd19_3_1321, List.forall_mem_cons.2 ⟨subd19_3_1322, List.forall_mem_cons.2 ⟨subd19_3_1323, List.forall_mem_cons.2 ⟨subd19_3_1324, List.forall_mem_cons.2 ⟨subd19_3_1325, List.forall_mem_cons.2 ⟨subd19_3_1326, List.forall_mem_cons.2 ⟨subd19_3_1327, List.forall_mem_cons.2 ⟨subd19_3_1328, List.forall_mem_cons.2 ⟨subd19_3_1329, List.forall_mem_cons.2 ⟨subd19_3_1330, List.forall_mem_cons.2 ⟨subd19_3_1331, List.forall_mem_cons.2 ⟨subd19_3_1332, List.forall_mem_cons.2 ⟨subd19_3_1333, List.forall_mem_cons.2 ⟨subd19_3_1334, List.forall_mem_cons.2 ⟨subd19_3_1335, List.forall_mem_cons.2 ⟨subd19_3_1336, List.forall_mem_cons.2 ⟨subd19_3_1337, List.forall_mem_cons.2 ⟨subd19_3_1338, List.forall_mem_cons.2 ⟨subd19_3_1339, List.forall_mem_cons.2 ⟨subd19_3_1340, List.forall_mem_cons.2 ⟨subd19_3_1341, List.forall_mem_cons.2 ⟨subd19_3_1342, List.forall_mem_cons.2 ⟨subd19_3_1343, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_3_1344 : subd19_3 [3, -4, -1] = true := by decide +kernel
theorem subd19_3_1345 : subd19_3 [3, -4, 0] = true := by decide +kernel
theorem subd19_3_1346 : subd19_3 [3, -4, 1] = true := by decide +kernel
theorem subd19_3_1347 : subd19_3 [3, -4, 2] = true := by decide +kernel
theorem subd19_3_1348 : subd19_3 [3, -4, 3] = true := by decide +kernel
theorem subd19_3_1349 : subd19_3 [3, -4, 4] = true := by decide +kernel
theorem subd19_3_1350 : subd19_3 [3, -4, 5] = true := by decide +kernel
theorem subd19_3_1351 : subd19_3 [3, -4, 6] = true := by decide +kernel
theorem subd19_3_1352 : subd19_3 [3, -4, 7] = true := by decide +kernel
theorem subd19_3_1353 : subd19_3 [3, -3, -8] = true := by decide +kernel
theorem subd19_3_1354 : subd19_3 [3, -3, -7] = true := by decide +kernel
theorem subd19_3_1355 : subd19_3 [3, -3, -6] = true := by decide +kernel
theorem subd19_3_1356 : subd19_3 [3, -3, -5] = true := by decide +kernel
theorem subd19_3_1357 : subd19_3 [3, -3, -4] = true := by decide +kernel
theorem subd19_3_1358 : subd19_3 [3, -3, -3] = true := by decide +kernel
theorem subd19_3_1359 : subd19_3 [3, -3, -2] = true := by decide +kernel
theorem subd19_3_1360 : subd19_3 [3, -3, -1] = true := by decide +kernel
theorem subd19_3_1361 : subd19_3 [3, -3, 0] = true := by decide +kernel
theorem subd19_3_1362 : subd19_3 [3, -3, 1] = true := by decide +kernel
theorem subd19_3_1363 : subd19_3 [3, -3, 2] = true := by decide +kernel
theorem subd19_3_1364 : subd19_3 [3, -3, 3] = true := by decide +kernel
theorem subd19_3_1365 : subd19_3 [3, -3, 4] = true := by decide +kernel
theorem subd19_3_1366 : subd19_3 [3, -3, 5] = true := by decide +kernel
theorem subd19_3_1367 : subd19_3 [3, -3, 6] = true := by decide +kernel
theorem subd19_3_1368 : subd19_3 [3, -3, 7] = true := by decide +kernel
theorem subd19_3_1369 : subd19_3 [3, -2, -9] = true := by decide +kernel
theorem subd19_3_1370 : subd19_3 [3, -2, -8] = true := by decide +kernel
theorem subd19_3_1371 : subd19_3 [3, -2, -7] = true := by decide +kernel
theorem subd19_3_1372 : subd19_3 [3, -2, -6] = true := by decide +kernel
theorem subd19_3_1373 : subd19_3 [3, -2, -5] = true := by decide +kernel
theorem subd19_3_1374 : subd19_3 [3, -2, -4] = true := by decide +kernel
theorem subd19_3_1375 : subd19_3 [3, -2, -3] = true := by decide +kernel
theorem sbd19_3_42 : ∀ q ∈ blkd19_3_42, subd19_3 q = true := by
  unfold blkd19_3_42
  exact List.forall_mem_cons.2 ⟨subd19_3_1344, List.forall_mem_cons.2 ⟨subd19_3_1345, List.forall_mem_cons.2 ⟨subd19_3_1346, List.forall_mem_cons.2 ⟨subd19_3_1347, List.forall_mem_cons.2 ⟨subd19_3_1348, List.forall_mem_cons.2 ⟨subd19_3_1349, List.forall_mem_cons.2 ⟨subd19_3_1350, List.forall_mem_cons.2 ⟨subd19_3_1351, List.forall_mem_cons.2 ⟨subd19_3_1352, List.forall_mem_cons.2 ⟨subd19_3_1353, List.forall_mem_cons.2 ⟨subd19_3_1354, List.forall_mem_cons.2 ⟨subd19_3_1355, List.forall_mem_cons.2 ⟨subd19_3_1356, List.forall_mem_cons.2 ⟨subd19_3_1357, List.forall_mem_cons.2 ⟨subd19_3_1358, List.forall_mem_cons.2 ⟨subd19_3_1359, List.forall_mem_cons.2 ⟨subd19_3_1360, List.forall_mem_cons.2 ⟨subd19_3_1361, List.forall_mem_cons.2 ⟨subd19_3_1362, List.forall_mem_cons.2 ⟨subd19_3_1363, List.forall_mem_cons.2 ⟨subd19_3_1364, List.forall_mem_cons.2 ⟨subd19_3_1365, List.forall_mem_cons.2 ⟨subd19_3_1366, List.forall_mem_cons.2 ⟨subd19_3_1367, List.forall_mem_cons.2 ⟨subd19_3_1368, List.forall_mem_cons.2 ⟨subd19_3_1369, List.forall_mem_cons.2 ⟨subd19_3_1370, List.forall_mem_cons.2 ⟨subd19_3_1371, List.forall_mem_cons.2 ⟨subd19_3_1372, List.forall_mem_cons.2 ⟨subd19_3_1373, List.forall_mem_cons.2 ⟨subd19_3_1374, List.forall_mem_cons.2 ⟨subd19_3_1375, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_3_1376 : subd19_3 [3, -2, -2] = true := by decide +kernel
theorem subd19_3_1377 : subd19_3 [3, -2, -1] = true := by decide +kernel
theorem subd19_3_1378 : subd19_3 [3, -2, 0] = true := by decide +kernel
theorem subd19_3_1379 : subd19_3 [3, -2, 1] = true := by decide +kernel
theorem subd19_3_1380 : subd19_3 [3, -2, 2] = true := by decide +kernel
theorem subd19_3_1381 : subd19_3 [3, -2, 3] = true := by decide +kernel
theorem subd19_3_1382 : subd19_3 [3, -2, 4] = true := by decide +kernel
theorem subd19_3_1383 : subd19_3 [3, -2, 5] = true := by decide +kernel
theorem subd19_3_1384 : subd19_3 [3, -2, 6] = true := by decide +kernel
theorem subd19_3_1385 : subd19_3 [3, -2, 7] = true := by decide +kernel
theorem subd19_3_1386 : subd19_3 [3, -1, -9] = true := by decide +kernel
theorem subd19_3_1387 : subd19_3 [3, -1, -8] = true := by decide +kernel
theorem subd19_3_1388 : subd19_3 [3, -1, -7] = true := by decide +kernel
theorem subd19_3_1389 : subd19_3 [3, -1, -6] = true := by decide +kernel
theorem subd19_3_1390 : subd19_3 [3, -1, -5] = true := by decide +kernel
theorem subd19_3_1391 : subd19_3 [3, -1, -4] = true := by decide +kernel
theorem subd19_3_1392 : subd19_3 [3, -1, -3] = true := by decide +kernel
theorem subd19_3_1393 : subd19_3 [3, -1, -2] = true := by decide +kernel
theorem subd19_3_1394 : subd19_3 [3, -1, -1] = true := by decide +kernel
theorem subd19_3_1395 : subd19_3 [3, -1, 0] = true := by decide +kernel
theorem subd19_3_1396 : subd19_3 [3, -1, 1] = true := by decide +kernel
theorem subd19_3_1397 : subd19_3 [3, -1, 2] = true := by decide +kernel
theorem subd19_3_1398 : subd19_3 [3, -1, 3] = true := by decide +kernel
theorem subd19_3_1399 : subd19_3 [3, -1, 4] = true := by decide +kernel
theorem subd19_3_1400 : subd19_3 [3, -1, 5] = true := by decide +kernel
theorem subd19_3_1401 : subd19_3 [3, -1, 6] = true := by decide +kernel
theorem subd19_3_1402 : subd19_3 [3, -1, 7] = true := by decide +kernel
theorem subd19_3_1403 : subd19_3 [3, 0, -10] = true := by decide +kernel
theorem subd19_3_1404 : subd19_3 [3, 0, -9] = true := by decide +kernel
theorem subd19_3_1405 : subd19_3 [3, 0, -8] = true := by decide +kernel
theorem subd19_3_1406 : subd19_3 [3, 0, -7] = true := by decide +kernel
theorem subd19_3_1407 : subd19_3 [3, 0, -6] = true := by decide +kernel
theorem sbd19_3_43 : ∀ q ∈ blkd19_3_43, subd19_3 q = true := by
  unfold blkd19_3_43
  exact List.forall_mem_cons.2 ⟨subd19_3_1376, List.forall_mem_cons.2 ⟨subd19_3_1377, List.forall_mem_cons.2 ⟨subd19_3_1378, List.forall_mem_cons.2 ⟨subd19_3_1379, List.forall_mem_cons.2 ⟨subd19_3_1380, List.forall_mem_cons.2 ⟨subd19_3_1381, List.forall_mem_cons.2 ⟨subd19_3_1382, List.forall_mem_cons.2 ⟨subd19_3_1383, List.forall_mem_cons.2 ⟨subd19_3_1384, List.forall_mem_cons.2 ⟨subd19_3_1385, List.forall_mem_cons.2 ⟨subd19_3_1386, List.forall_mem_cons.2 ⟨subd19_3_1387, List.forall_mem_cons.2 ⟨subd19_3_1388, List.forall_mem_cons.2 ⟨subd19_3_1389, List.forall_mem_cons.2 ⟨subd19_3_1390, List.forall_mem_cons.2 ⟨subd19_3_1391, List.forall_mem_cons.2 ⟨subd19_3_1392, List.forall_mem_cons.2 ⟨subd19_3_1393, List.forall_mem_cons.2 ⟨subd19_3_1394, List.forall_mem_cons.2 ⟨subd19_3_1395, List.forall_mem_cons.2 ⟨subd19_3_1396, List.forall_mem_cons.2 ⟨subd19_3_1397, List.forall_mem_cons.2 ⟨subd19_3_1398, List.forall_mem_cons.2 ⟨subd19_3_1399, List.forall_mem_cons.2 ⟨subd19_3_1400, List.forall_mem_cons.2 ⟨subd19_3_1401, List.forall_mem_cons.2 ⟨subd19_3_1402, List.forall_mem_cons.2 ⟨subd19_3_1403, List.forall_mem_cons.2 ⟨subd19_3_1404, List.forall_mem_cons.2 ⟨subd19_3_1405, List.forall_mem_cons.2 ⟨subd19_3_1406, List.forall_mem_cons.2 ⟨subd19_3_1407, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_3_1408 : subd19_3 [3, 0, -5] = true := by decide +kernel
theorem subd19_3_1409 : subd19_3 [3, 0, -4] = true := by decide +kernel
theorem subd19_3_1410 : subd19_3 [3, 0, -3] = true := by decide +kernel
theorem subd19_3_1411 : subd19_3 [3, 0, -2] = true := by decide +kernel
theorem subd19_3_1412 : subd19_3 [3, 0, -1] = true := by decide +kernel
theorem subd19_3_1413 : subd19_3 [3, 0, 0] = true := by decide +kernel
theorem subd19_3_1414 : subd19_3 [3, 0, 1] = true := by decide +kernel
theorem subd19_3_1415 : subd19_3 [3, 0, 2] = true := by decide +kernel
theorem subd19_3_1416 : subd19_3 [3, 0, 3] = true := by decide +kernel
theorem subd19_3_1417 : subd19_3 [3, 0, 4] = true := by decide +kernel
theorem subd19_3_1418 : subd19_3 [3, 0, 5] = true := by decide +kernel
theorem subd19_3_1419 : subd19_3 [3, 0, 6] = true := by decide +kernel
theorem subd19_3_1420 : subd19_3 [3, 0, 7] = true := by decide +kernel
theorem subd19_3_1421 : subd19_3 [3, 1, -10] = true := by decide +kernel
theorem subd19_3_1422 : subd19_3 [3, 1, -9] = true := by decide +kernel
theorem subd19_3_1423 : subd19_3 [3, 1, -8] = true := by decide +kernel
theorem subd19_3_1424 : subd19_3 [3, 1, -7] = true := by decide +kernel
theorem subd19_3_1425 : subd19_3 [3, 1, -6] = true := by decide +kernel
theorem subd19_3_1426 : subd19_3 [3, 1, -5] = true := by decide +kernel
theorem subd19_3_1427 : subd19_3 [3, 1, -4] = true := by decide +kernel
theorem subd19_3_1428 : subd19_3 [3, 1, -3] = true := by decide +kernel
theorem subd19_3_1429 : subd19_3 [3, 1, -2] = true := by decide +kernel
theorem subd19_3_1430 : subd19_3 [3, 1, -1] = true := by decide +kernel
theorem subd19_3_1431 : subd19_3 [3, 1, 0] = true := by decide +kernel
theorem subd19_3_1432 : subd19_3 [3, 1, 1] = true := by decide +kernel
theorem subd19_3_1433 : subd19_3 [3, 1, 2] = true := by decide +kernel
theorem subd19_3_1434 : subd19_3 [3, 1, 3] = true := by decide +kernel
theorem subd19_3_1435 : subd19_3 [3, 1, 4] = true := by decide +kernel
theorem subd19_3_1436 : subd19_3 [3, 1, 5] = true := by decide +kernel
theorem subd19_3_1437 : subd19_3 [3, 1, 6] = true := by decide +kernel
theorem subd19_3_1438 : subd19_3 [3, 2, -10] = true := by decide +kernel
theorem subd19_3_1439 : subd19_3 [3, 2, -9] = true := by decide +kernel
theorem sbd19_3_44 : ∀ q ∈ blkd19_3_44, subd19_3 q = true := by
  unfold blkd19_3_44
  exact List.forall_mem_cons.2 ⟨subd19_3_1408, List.forall_mem_cons.2 ⟨subd19_3_1409, List.forall_mem_cons.2 ⟨subd19_3_1410, List.forall_mem_cons.2 ⟨subd19_3_1411, List.forall_mem_cons.2 ⟨subd19_3_1412, List.forall_mem_cons.2 ⟨subd19_3_1413, List.forall_mem_cons.2 ⟨subd19_3_1414, List.forall_mem_cons.2 ⟨subd19_3_1415, List.forall_mem_cons.2 ⟨subd19_3_1416, List.forall_mem_cons.2 ⟨subd19_3_1417, List.forall_mem_cons.2 ⟨subd19_3_1418, List.forall_mem_cons.2 ⟨subd19_3_1419, List.forall_mem_cons.2 ⟨subd19_3_1420, List.forall_mem_cons.2 ⟨subd19_3_1421, List.forall_mem_cons.2 ⟨subd19_3_1422, List.forall_mem_cons.2 ⟨subd19_3_1423, List.forall_mem_cons.2 ⟨subd19_3_1424, List.forall_mem_cons.2 ⟨subd19_3_1425, List.forall_mem_cons.2 ⟨subd19_3_1426, List.forall_mem_cons.2 ⟨subd19_3_1427, List.forall_mem_cons.2 ⟨subd19_3_1428, List.forall_mem_cons.2 ⟨subd19_3_1429, List.forall_mem_cons.2 ⟨subd19_3_1430, List.forall_mem_cons.2 ⟨subd19_3_1431, List.forall_mem_cons.2 ⟨subd19_3_1432, List.forall_mem_cons.2 ⟨subd19_3_1433, List.forall_mem_cons.2 ⟨subd19_3_1434, List.forall_mem_cons.2 ⟨subd19_3_1435, List.forall_mem_cons.2 ⟨subd19_3_1436, List.forall_mem_cons.2 ⟨subd19_3_1437, List.forall_mem_cons.2 ⟨subd19_3_1438, List.forall_mem_cons.2 ⟨subd19_3_1439, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
