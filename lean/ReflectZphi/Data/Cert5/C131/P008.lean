import ReflectZphi.Data.Cert5.C131.Base

namespace ReflectZphi.Data.Cert5.C131

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_0_928 : subd9_0 [2, 1, -4] = true := by decide +kernel
theorem subd9_0_929 : subd9_0 [2, 1, -3] = true := by decide +kernel
theorem subd9_0_930 : subd9_0 [2, 1, -2] = true := by decide +kernel
theorem subd9_0_931 : subd9_0 [2, 1, -1] = true := by decide +kernel
theorem subd9_0_932 : subd9_0 [2, 1, 0] = true := by decide +kernel
theorem subd9_0_933 : subd9_0 [2, 1, 1] = true := by decide +kernel
theorem subd9_0_934 : subd9_0 [2, 1, 2] = true := by decide +kernel
theorem subd9_0_935 : subd9_0 [2, 1, 3] = true := by decide +kernel
theorem subd9_0_936 : subd9_0 [2, 1, 4] = true := by decide +kernel
theorem subd9_0_937 : subd9_0 [2, 1, 5] = true := by decide +kernel
theorem subd9_0_938 : subd9_0 [2, 1, 6] = true := by decide +kernel
theorem subd9_0_939 : subd9_0 [2, 1, 7] = true := by decide +kernel
theorem subd9_0_940 : subd9_0 [2, 1, 8] = true := by decide +kernel
theorem subd9_0_941 : subd9_0 [2, 1, 9] = true := by decide +kernel
theorem subd9_0_942 : subd9_0 [2, 2, -10] = true := by decide +kernel
theorem subd9_0_943 : subd9_0 [2, 2, -9] = true := by decide +kernel
theorem subd9_0_944 : subd9_0 [2, 2, -8] = true := by decide +kernel
theorem subd9_0_945 : subd9_0 [2, 2, -7] = true := by decide +kernel
theorem subd9_0_946 : subd9_0 [2, 2, -6] = true := by decide +kernel
theorem subd9_0_947 : subd9_0 [2, 2, -5] = true := by decide +kernel
theorem subd9_0_948 : subd9_0 [2, 2, -4] = true := by decide +kernel
theorem subd9_0_949 : subd9_0 [2, 2, -3] = true := by decide +kernel
theorem subd9_0_950 : subd9_0 [2, 2, -2] = true := by decide +kernel
theorem subd9_0_951 : subd9_0 [2, 2, -1] = true := by decide +kernel
theorem subd9_0_952 : subd9_0 [2, 2, 0] = true := by decide +kernel
theorem subd9_0_953 : subd9_0 [2, 2, 1] = true := by decide +kernel
theorem subd9_0_954 : subd9_0 [2, 2, 2] = true := by decide +kernel
theorem subd9_0_955 : subd9_0 [2, 2, 3] = true := by decide +kernel
theorem subd9_0_956 : subd9_0 [2, 2, 4] = true := by decide +kernel
theorem subd9_0_957 : subd9_0 [2, 2, 5] = true := by decide +kernel
theorem subd9_0_958 : subd9_0 [2, 2, 6] = true := by decide +kernel
theorem subd9_0_959 : subd9_0 [2, 2, 7] = true := by decide +kernel
theorem sbd9_0_29 : ∀ q ∈ blkd9_0_29, subd9_0 q = true := by
  unfold blkd9_0_29
  exact List.forall_mem_cons.2 ⟨subd9_0_928, List.forall_mem_cons.2 ⟨subd9_0_929, List.forall_mem_cons.2 ⟨subd9_0_930, List.forall_mem_cons.2 ⟨subd9_0_931, List.forall_mem_cons.2 ⟨subd9_0_932, List.forall_mem_cons.2 ⟨subd9_0_933, List.forall_mem_cons.2 ⟨subd9_0_934, List.forall_mem_cons.2 ⟨subd9_0_935, List.forall_mem_cons.2 ⟨subd9_0_936, List.forall_mem_cons.2 ⟨subd9_0_937, List.forall_mem_cons.2 ⟨subd9_0_938, List.forall_mem_cons.2 ⟨subd9_0_939, List.forall_mem_cons.2 ⟨subd9_0_940, List.forall_mem_cons.2 ⟨subd9_0_941, List.forall_mem_cons.2 ⟨subd9_0_942, List.forall_mem_cons.2 ⟨subd9_0_943, List.forall_mem_cons.2 ⟨subd9_0_944, List.forall_mem_cons.2 ⟨subd9_0_945, List.forall_mem_cons.2 ⟨subd9_0_946, List.forall_mem_cons.2 ⟨subd9_0_947, List.forall_mem_cons.2 ⟨subd9_0_948, List.forall_mem_cons.2 ⟨subd9_0_949, List.forall_mem_cons.2 ⟨subd9_0_950, List.forall_mem_cons.2 ⟨subd9_0_951, List.forall_mem_cons.2 ⟨subd9_0_952, List.forall_mem_cons.2 ⟨subd9_0_953, List.forall_mem_cons.2 ⟨subd9_0_954, List.forall_mem_cons.2 ⟨subd9_0_955, List.forall_mem_cons.2 ⟨subd9_0_956, List.forall_mem_cons.2 ⟨subd9_0_957, List.forall_mem_cons.2 ⟨subd9_0_958, List.forall_mem_cons.2 ⟨subd9_0_959, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_0_960 : subd9_0 [2, 2, 8] = true := by decide +kernel
theorem subd9_0_961 : subd9_0 [2, 2, 9] = true := by decide +kernel
theorem subd9_0_962 : subd9_0 [2, 3, -10] = true := by decide +kernel
theorem subd9_0_963 : subd9_0 [2, 3, -9] = true := by decide +kernel
theorem subd9_0_964 : subd9_0 [2, 3, -8] = true := by decide +kernel
theorem subd9_0_965 : subd9_0 [2, 3, -7] = true := by decide +kernel
theorem subd9_0_966 : subd9_0 [2, 3, -6] = true := by decide +kernel
theorem subd9_0_967 : subd9_0 [2, 3, -5] = true := by decide +kernel
theorem subd9_0_968 : subd9_0 [2, 3, -4] = true := by decide +kernel
theorem subd9_0_969 : subd9_0 [2, 3, -3] = true := by decide +kernel
theorem subd9_0_970 : subd9_0 [2, 3, -2] = true := by decide +kernel
theorem subd9_0_971 : subd9_0 [2, 3, -1] = true := by decide +kernel
theorem subd9_0_972 : subd9_0 [2, 3, 0] = true := by decide +kernel
theorem subd9_0_973 : subd9_0 [2, 3, 1] = true := by decide +kernel
theorem subd9_0_974 : subd9_0 [2, 3, 2] = true := by decide +kernel
theorem subd9_0_975 : subd9_0 [2, 3, 3] = true := by decide +kernel
theorem subd9_0_976 : subd9_0 [2, 3, 4] = true := by decide +kernel
theorem subd9_0_977 : subd9_0 [2, 3, 5] = true := by decide +kernel
theorem subd9_0_978 : subd9_0 [2, 3, 6] = true := by decide +kernel
theorem subd9_0_979 : subd9_0 [2, 3, 7] = true := by decide +kernel
theorem subd9_0_980 : subd9_0 [2, 3, 8] = true := by decide +kernel
theorem subd9_0_981 : subd9_0 [2, 4, -9] = true := by decide +kernel
theorem subd9_0_982 : subd9_0 [2, 4, -8] = true := by decide +kernel
theorem subd9_0_983 : subd9_0 [2, 4, -7] = true := by decide +kernel
theorem subd9_0_984 : subd9_0 [2, 4, -6] = true := by decide +kernel
theorem subd9_0_985 : subd9_0 [2, 4, -5] = true := by decide +kernel
theorem subd9_0_986 : subd9_0 [2, 4, -4] = true := by decide +kernel
theorem subd9_0_987 : subd9_0 [2, 4, -3] = true := by decide +kernel
theorem subd9_0_988 : subd9_0 [2, 4, -2] = true := by decide +kernel
theorem subd9_0_989 : subd9_0 [2, 4, -1] = true := by decide +kernel
theorem subd9_0_990 : subd9_0 [2, 4, 0] = true := by decide +kernel
theorem subd9_0_991 : subd9_0 [2, 4, 1] = true := by decide +kernel
theorem sbd9_0_30 : ∀ q ∈ blkd9_0_30, subd9_0 q = true := by
  unfold blkd9_0_30
  exact List.forall_mem_cons.2 ⟨subd9_0_960, List.forall_mem_cons.2 ⟨subd9_0_961, List.forall_mem_cons.2 ⟨subd9_0_962, List.forall_mem_cons.2 ⟨subd9_0_963, List.forall_mem_cons.2 ⟨subd9_0_964, List.forall_mem_cons.2 ⟨subd9_0_965, List.forall_mem_cons.2 ⟨subd9_0_966, List.forall_mem_cons.2 ⟨subd9_0_967, List.forall_mem_cons.2 ⟨subd9_0_968, List.forall_mem_cons.2 ⟨subd9_0_969, List.forall_mem_cons.2 ⟨subd9_0_970, List.forall_mem_cons.2 ⟨subd9_0_971, List.forall_mem_cons.2 ⟨subd9_0_972, List.forall_mem_cons.2 ⟨subd9_0_973, List.forall_mem_cons.2 ⟨subd9_0_974, List.forall_mem_cons.2 ⟨subd9_0_975, List.forall_mem_cons.2 ⟨subd9_0_976, List.forall_mem_cons.2 ⟨subd9_0_977, List.forall_mem_cons.2 ⟨subd9_0_978, List.forall_mem_cons.2 ⟨subd9_0_979, List.forall_mem_cons.2 ⟨subd9_0_980, List.forall_mem_cons.2 ⟨subd9_0_981, List.forall_mem_cons.2 ⟨subd9_0_982, List.forall_mem_cons.2 ⟨subd9_0_983, List.forall_mem_cons.2 ⟨subd9_0_984, List.forall_mem_cons.2 ⟨subd9_0_985, List.forall_mem_cons.2 ⟨subd9_0_986, List.forall_mem_cons.2 ⟨subd9_0_987, List.forall_mem_cons.2 ⟨subd9_0_988, List.forall_mem_cons.2 ⟨subd9_0_989, List.forall_mem_cons.2 ⟨subd9_0_990, List.forall_mem_cons.2 ⟨subd9_0_991, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_0_992 : subd9_0 [2, 4, 2] = true := by decide +kernel
theorem subd9_0_993 : subd9_0 [2, 4, 3] = true := by decide +kernel
theorem subd9_0_994 : subd9_0 [2, 4, 4] = true := by decide +kernel
theorem subd9_0_995 : subd9_0 [2, 4, 5] = true := by decide +kernel
theorem subd9_0_996 : subd9_0 [2, 4, 6] = true := by decide +kernel
theorem subd9_0_997 : subd9_0 [2, 5, -8] = true := by decide +kernel
theorem subd9_0_998 : subd9_0 [2, 5, -7] = true := by decide +kernel
theorem subd9_0_999 : subd9_0 [2, 5, -6] = true := by decide +kernel
theorem subd9_0_1000 : subd9_0 [2, 5, -5] = true := by decide +kernel
theorem subd9_0_1001 : subd9_0 [2, 5, -4] = true := by decide +kernel
theorem subd9_0_1002 : subd9_0 [2, 5, -3] = true := by decide +kernel
theorem subd9_0_1003 : subd9_0 [2, 5, -2] = true := by decide +kernel
theorem subd9_0_1004 : subd9_0 [2, 5, -1] = true := by decide +kernel
theorem subd9_0_1005 : subd9_0 [2, 5, 0] = true := by decide +kernel
theorem subd9_0_1006 : subd9_0 [2, 5, 1] = true := by decide +kernel
theorem subd9_0_1007 : subd9_0 [2, 5, 2] = true := by decide +kernel
theorem subd9_0_1008 : subd9_0 [2, 5, 3] = true := by decide +kernel
theorem subd9_0_1009 : subd9_0 [2, 5, 4] = true := by decide +kernel
theorem subd9_0_1010 : subd9_0 [2, 6] = true := by decide +kernel
theorem subd9_0_1011 : subd9_0 [3, -4] = true := by decide +kernel
theorem subd9_0_1012 : subd9_0 [3, -3] = true := by decide +kernel
theorem subd9_0_1013 : subd9_0 [3, -2] = true := by decide +kernel
theorem subd9_0_1014 : subd9_0 [3, -1, -6] = true := by decide +kernel
theorem subd9_0_1015 : subd9_0 [3, -1, -5] = true := by decide +kernel
theorem subd9_0_1016 : subd9_0 [3, -1, -4] = true := by decide +kernel
theorem subd9_0_1017 : subd9_0 [3, -1, -3] = true := by decide +kernel
theorem subd9_0_1018 : subd9_0 [3, -1, -2] = true := by decide +kernel
theorem subd9_0_1019 : subd9_0 [3, -1, -1] = true := by decide +kernel
theorem subd9_0_1020 : subd9_0 [3, -1, 0] = true := by decide +kernel
theorem subd9_0_1021 : subd9_0 [3, -1, 1] = true := by decide +kernel
theorem subd9_0_1022 : subd9_0 [3, -1, 2] = true := by decide +kernel
theorem subd9_0_1023 : subd9_0 [3, -1, 3] = true := by decide +kernel
theorem sbd9_0_31 : ∀ q ∈ blkd9_0_31, subd9_0 q = true := by
  unfold blkd9_0_31
  exact List.forall_mem_cons.2 ⟨subd9_0_992, List.forall_mem_cons.2 ⟨subd9_0_993, List.forall_mem_cons.2 ⟨subd9_0_994, List.forall_mem_cons.2 ⟨subd9_0_995, List.forall_mem_cons.2 ⟨subd9_0_996, List.forall_mem_cons.2 ⟨subd9_0_997, List.forall_mem_cons.2 ⟨subd9_0_998, List.forall_mem_cons.2 ⟨subd9_0_999, List.forall_mem_cons.2 ⟨subd9_0_1000, List.forall_mem_cons.2 ⟨subd9_0_1001, List.forall_mem_cons.2 ⟨subd9_0_1002, List.forall_mem_cons.2 ⟨subd9_0_1003, List.forall_mem_cons.2 ⟨subd9_0_1004, List.forall_mem_cons.2 ⟨subd9_0_1005, List.forall_mem_cons.2 ⟨subd9_0_1006, List.forall_mem_cons.2 ⟨subd9_0_1007, List.forall_mem_cons.2 ⟨subd9_0_1008, List.forall_mem_cons.2 ⟨subd9_0_1009, List.forall_mem_cons.2 ⟨subd9_0_1010, List.forall_mem_cons.2 ⟨subd9_0_1011, List.forall_mem_cons.2 ⟨subd9_0_1012, List.forall_mem_cons.2 ⟨subd9_0_1013, List.forall_mem_cons.2 ⟨subd9_0_1014, List.forall_mem_cons.2 ⟨subd9_0_1015, List.forall_mem_cons.2 ⟨subd9_0_1016, List.forall_mem_cons.2 ⟨subd9_0_1017, List.forall_mem_cons.2 ⟨subd9_0_1018, List.forall_mem_cons.2 ⟨subd9_0_1019, List.forall_mem_cons.2 ⟨subd9_0_1020, List.forall_mem_cons.2 ⟨subd9_0_1021, List.forall_mem_cons.2 ⟨subd9_0_1022, List.forall_mem_cons.2 ⟨subd9_0_1023, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_0_1024 : subd9_0 [3, -1, 4] = true := by decide +kernel
theorem subd9_0_1025 : subd9_0 [3, -1, 5] = true := by decide +kernel
theorem subd9_0_1026 : subd9_0 [3, -1, 6] = true := by decide +kernel
theorem subd9_0_1027 : subd9_0 [3, -1, 7] = true := by decide +kernel
theorem subd9_0_1028 : subd9_0 [3, -1, 8] = true := by decide +kernel
theorem subd9_0_1029 : subd9_0 [3, -1, 9] = true := by decide +kernel
theorem subd9_0_1030 : subd9_0 [3, 0, -7] = true := by decide +kernel
theorem subd9_0_1031 : subd9_0 [3, 0, -6] = true := by decide +kernel
theorem subd9_0_1032 : subd9_0 [3, 0, -5] = true := by decide +kernel
theorem subd9_0_1033 : subd9_0 [3, 0, -4] = true := by decide +kernel
theorem subd9_0_1034 : subd9_0 [3, 0, -3] = true := by decide +kernel
theorem subd9_0_1035 : subd9_0 [3, 0, -2] = true := by decide +kernel
theorem subd9_0_1036 : subd9_0 [3, 0, -1] = true := by decide +kernel
theorem subd9_0_1037 : subd9_0 [3, 0, 0] = true := by decide +kernel
theorem subd9_0_1038 : subd9_0 [3, 0, 1] = true := by decide +kernel
theorem subd9_0_1039 : subd9_0 [3, 0, 2] = true := by decide +kernel
theorem subd9_0_1040 : subd9_0 [3, 0, 3] = true := by decide +kernel
theorem subd9_0_1041 : subd9_0 [3, 0, 4] = true := by decide +kernel
theorem subd9_0_1042 : subd9_0 [3, 0, 5] = true := by decide +kernel
theorem subd9_0_1043 : subd9_0 [3, 0, 6] = true := by decide +kernel
theorem subd9_0_1044 : subd9_0 [3, 0, 7] = true := by decide +kernel
theorem subd9_0_1045 : subd9_0 [3, 0, 8] = true := by decide +kernel
theorem subd9_0_1046 : subd9_0 [3, 0, 9] = true := by decide +kernel
theorem subd9_0_1047 : subd9_0 [3, 1, -8] = true := by decide +kernel
theorem subd9_0_1048 : subd9_0 [3, 1, -7] = true := by decide +kernel
theorem subd9_0_1049 : subd9_0 [3, 1, -6] = true := by decide +kernel
theorem subd9_0_1050 : subd9_0 [3, 1, -5] = true := by decide +kernel
theorem subd9_0_1051 : subd9_0 [3, 1, -4] = true := by decide +kernel
theorem subd9_0_1052 : subd9_0 [3, 1, -3] = true := by decide +kernel
theorem subd9_0_1053 : subd9_0 [3, 1, -2] = true := by decide +kernel
theorem subd9_0_1054 : subd9_0 [3, 1, -1] = true := by decide +kernel
theorem subd9_0_1055 : subd9_0 [3, 1, 0] = true := by decide +kernel
theorem sbd9_0_32 : ∀ q ∈ blkd9_0_32, subd9_0 q = true := by
  unfold blkd9_0_32
  exact List.forall_mem_cons.2 ⟨subd9_0_1024, List.forall_mem_cons.2 ⟨subd9_0_1025, List.forall_mem_cons.2 ⟨subd9_0_1026, List.forall_mem_cons.2 ⟨subd9_0_1027, List.forall_mem_cons.2 ⟨subd9_0_1028, List.forall_mem_cons.2 ⟨subd9_0_1029, List.forall_mem_cons.2 ⟨subd9_0_1030, List.forall_mem_cons.2 ⟨subd9_0_1031, List.forall_mem_cons.2 ⟨subd9_0_1032, List.forall_mem_cons.2 ⟨subd9_0_1033, List.forall_mem_cons.2 ⟨subd9_0_1034, List.forall_mem_cons.2 ⟨subd9_0_1035, List.forall_mem_cons.2 ⟨subd9_0_1036, List.forall_mem_cons.2 ⟨subd9_0_1037, List.forall_mem_cons.2 ⟨subd9_0_1038, List.forall_mem_cons.2 ⟨subd9_0_1039, List.forall_mem_cons.2 ⟨subd9_0_1040, List.forall_mem_cons.2 ⟨subd9_0_1041, List.forall_mem_cons.2 ⟨subd9_0_1042, List.forall_mem_cons.2 ⟨subd9_0_1043, List.forall_mem_cons.2 ⟨subd9_0_1044, List.forall_mem_cons.2 ⟨subd9_0_1045, List.forall_mem_cons.2 ⟨subd9_0_1046, List.forall_mem_cons.2 ⟨subd9_0_1047, List.forall_mem_cons.2 ⟨subd9_0_1048, List.forall_mem_cons.2 ⟨subd9_0_1049, List.forall_mem_cons.2 ⟨subd9_0_1050, List.forall_mem_cons.2 ⟨subd9_0_1051, List.forall_mem_cons.2 ⟨subd9_0_1052, List.forall_mem_cons.2 ⟨subd9_0_1053, List.forall_mem_cons.2 ⟨subd9_0_1054, List.forall_mem_cons.2 ⟨subd9_0_1055, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_0_1056 : subd9_0 [3, 1, 1] = true := by decide +kernel
theorem subd9_0_1057 : subd9_0 [3, 1, 2] = true := by decide +kernel
theorem subd9_0_1058 : subd9_0 [3, 1, 3] = true := by decide +kernel
theorem subd9_0_1059 : subd9_0 [3, 1, 4] = true := by decide +kernel
theorem subd9_0_1060 : subd9_0 [3, 1, 5] = true := by decide +kernel
theorem subd9_0_1061 : subd9_0 [3, 1, 6] = true := by decide +kernel
theorem subd9_0_1062 : subd9_0 [3, 1, 7] = true := by decide +kernel
theorem subd9_0_1063 : subd9_0 [3, 1, 8] = true := by decide +kernel
theorem subd9_0_1064 : subd9_0 [3, 1, 9] = true := by decide +kernel
theorem subd9_0_1065 : subd9_0 [3, 2, -8] = true := by decide +kernel
theorem subd9_0_1066 : subd9_0 [3, 2, -7] = true := by decide +kernel
theorem subd9_0_1067 : subd9_0 [3, 2, -6] = true := by decide +kernel
theorem subd9_0_1068 : subd9_0 [3, 2, -5] = true := by decide +kernel
theorem subd9_0_1069 : subd9_0 [3, 2, -4] = true := by decide +kernel
theorem subd9_0_1070 : subd9_0 [3, 2, -3] = true := by decide +kernel
theorem subd9_0_1071 : subd9_0 [3, 2, -2] = true := by decide +kernel
theorem subd9_0_1072 : subd9_0 [3, 2, -1] = true := by decide +kernel
theorem subd9_0_1073 : subd9_0 [3, 2, 0] = true := by decide +kernel
theorem subd9_0_1074 : subd9_0 [3, 2, 1] = true := by decide +kernel
theorem subd9_0_1075 : subd9_0 [3, 2, 2] = true := by decide +kernel
theorem subd9_0_1076 : subd9_0 [3, 2, 3] = true := by decide +kernel
theorem subd9_0_1077 : subd9_0 [3, 2, 4] = true := by decide +kernel
theorem subd9_0_1078 : subd9_0 [3, 2, 5] = true := by decide +kernel
theorem subd9_0_1079 : subd9_0 [3, 2, 6] = true := by decide +kernel
theorem subd9_0_1080 : subd9_0 [3, 2, 7] = true := by decide +kernel
theorem subd9_0_1081 : subd9_0 [3, 2, 8] = true := by decide +kernel
theorem subd9_0_1082 : subd9_0 [3, 3, -8] = true := by decide +kernel
theorem subd9_0_1083 : subd9_0 [3, 3, -7] = true := by decide +kernel
theorem subd9_0_1084 : subd9_0 [3, 3, -6] = true := by decide +kernel
theorem subd9_0_1085 : subd9_0 [3, 3, -5] = true := by decide +kernel
theorem subd9_0_1086 : subd9_0 [3, 3, -4] = true := by decide +kernel
theorem subd9_0_1087 : subd9_0 [3, 3, -3] = true := by decide +kernel
theorem sbd9_0_33 : ∀ q ∈ blkd9_0_33, subd9_0 q = true := by
  unfold blkd9_0_33
  exact List.forall_mem_cons.2 ⟨subd9_0_1056, List.forall_mem_cons.2 ⟨subd9_0_1057, List.forall_mem_cons.2 ⟨subd9_0_1058, List.forall_mem_cons.2 ⟨subd9_0_1059, List.forall_mem_cons.2 ⟨subd9_0_1060, List.forall_mem_cons.2 ⟨subd9_0_1061, List.forall_mem_cons.2 ⟨subd9_0_1062, List.forall_mem_cons.2 ⟨subd9_0_1063, List.forall_mem_cons.2 ⟨subd9_0_1064, List.forall_mem_cons.2 ⟨subd9_0_1065, List.forall_mem_cons.2 ⟨subd9_0_1066, List.forall_mem_cons.2 ⟨subd9_0_1067, List.forall_mem_cons.2 ⟨subd9_0_1068, List.forall_mem_cons.2 ⟨subd9_0_1069, List.forall_mem_cons.2 ⟨subd9_0_1070, List.forall_mem_cons.2 ⟨subd9_0_1071, List.forall_mem_cons.2 ⟨subd9_0_1072, List.forall_mem_cons.2 ⟨subd9_0_1073, List.forall_mem_cons.2 ⟨subd9_0_1074, List.forall_mem_cons.2 ⟨subd9_0_1075, List.forall_mem_cons.2 ⟨subd9_0_1076, List.forall_mem_cons.2 ⟨subd9_0_1077, List.forall_mem_cons.2 ⟨subd9_0_1078, List.forall_mem_cons.2 ⟨subd9_0_1079, List.forall_mem_cons.2 ⟨subd9_0_1080, List.forall_mem_cons.2 ⟨subd9_0_1081, List.forall_mem_cons.2 ⟨subd9_0_1082, List.forall_mem_cons.2 ⟨subd9_0_1083, List.forall_mem_cons.2 ⟨subd9_0_1084, List.forall_mem_cons.2 ⟨subd9_0_1085, List.forall_mem_cons.2 ⟨subd9_0_1086, List.forall_mem_cons.2 ⟨subd9_0_1087, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_0_1088 : subd9_0 [3, 3, -2] = true := by decide +kernel
theorem subd9_0_1089 : subd9_0 [3, 3, -1] = true := by decide +kernel
theorem subd9_0_1090 : subd9_0 [3, 3, 0] = true := by decide +kernel
theorem subd9_0_1091 : subd9_0 [3, 3, 1] = true := by decide +kernel
theorem subd9_0_1092 : subd9_0 [3, 3, 2] = true := by decide +kernel
theorem subd9_0_1093 : subd9_0 [3, 3, 3] = true := by decide +kernel
theorem subd9_0_1094 : subd9_0 [3, 3, 4] = true := by decide +kernel
theorem subd9_0_1095 : subd9_0 [3, 3, 5] = true := by decide +kernel
theorem subd9_0_1096 : subd9_0 [3, 3, 6] = true := by decide +kernel
theorem subd9_0_1097 : subd9_0 [3, 3, 7] = true := by decide +kernel
theorem subd9_0_1098 : subd9_0 [3, 4, -8] = true := by decide +kernel
theorem subd9_0_1099 : subd9_0 [3, 4, -7] = true := by decide +kernel
theorem subd9_0_1100 : subd9_0 [3, 4, -6] = true := by decide +kernel
theorem subd9_0_1101 : subd9_0 [3, 4, -5] = true := by decide +kernel
theorem subd9_0_1102 : subd9_0 [3, 4, -4] = true := by decide +kernel
theorem subd9_0_1103 : subd9_0 [3, 4, -3] = true := by decide +kernel
theorem subd9_0_1104 : subd9_0 [3, 4, -2] = true := by decide +kernel
theorem subd9_0_1105 : subd9_0 [3, 4, -1] = true := by decide +kernel
theorem subd9_0_1106 : subd9_0 [3, 4, 0] = true := by decide +kernel
theorem subd9_0_1107 : subd9_0 [3, 4, 1] = true := by decide +kernel
theorem subd9_0_1108 : subd9_0 [3, 4, 2] = true := by decide +kernel
theorem subd9_0_1109 : subd9_0 [3, 4, 3] = true := by decide +kernel
theorem subd9_0_1110 : subd9_0 [3, 4, 4] = true := by decide +kernel
theorem subd9_0_1111 : subd9_0 [3, 4, 5] = true := by decide +kernel
theorem subd9_0_1112 : subd9_0 [3, 4, 6] = true := by decide +kernel
theorem subd9_0_1113 : subd9_0 [3, 5] = true := by decide +kernel
theorem subd9_0_1114 : subd9_0 [3, 6] = true := by decide +kernel
theorem subd9_0_1115 : subd9_0 [4, -3] = true := by decide +kernel
theorem subd9_0_1116 : subd9_0 [4, -2] = true := by decide +kernel
theorem subd9_0_1117 : subd9_0 [4, -1] = true := by decide +kernel
theorem subd9_0_1118 : subd9_0 [4, 0] = true := by decide +kernel
theorem subd9_0_1119 : subd9_0 [4, 1, -6] = true := by decide +kernel
theorem sbd9_0_34 : ∀ q ∈ blkd9_0_34, subd9_0 q = true := by
  unfold blkd9_0_34
  exact List.forall_mem_cons.2 ⟨subd9_0_1088, List.forall_mem_cons.2 ⟨subd9_0_1089, List.forall_mem_cons.2 ⟨subd9_0_1090, List.forall_mem_cons.2 ⟨subd9_0_1091, List.forall_mem_cons.2 ⟨subd9_0_1092, List.forall_mem_cons.2 ⟨subd9_0_1093, List.forall_mem_cons.2 ⟨subd9_0_1094, List.forall_mem_cons.2 ⟨subd9_0_1095, List.forall_mem_cons.2 ⟨subd9_0_1096, List.forall_mem_cons.2 ⟨subd9_0_1097, List.forall_mem_cons.2 ⟨subd9_0_1098, List.forall_mem_cons.2 ⟨subd9_0_1099, List.forall_mem_cons.2 ⟨subd9_0_1100, List.forall_mem_cons.2 ⟨subd9_0_1101, List.forall_mem_cons.2 ⟨subd9_0_1102, List.forall_mem_cons.2 ⟨subd9_0_1103, List.forall_mem_cons.2 ⟨subd9_0_1104, List.forall_mem_cons.2 ⟨subd9_0_1105, List.forall_mem_cons.2 ⟨subd9_0_1106, List.forall_mem_cons.2 ⟨subd9_0_1107, List.forall_mem_cons.2 ⟨subd9_0_1108, List.forall_mem_cons.2 ⟨subd9_0_1109, List.forall_mem_cons.2 ⟨subd9_0_1110, List.forall_mem_cons.2 ⟨subd9_0_1111, List.forall_mem_cons.2 ⟨subd9_0_1112, List.forall_mem_cons.2 ⟨subd9_0_1113, List.forall_mem_cons.2 ⟨subd9_0_1114, List.forall_mem_cons.2 ⟨subd9_0_1115, List.forall_mem_cons.2 ⟨subd9_0_1116, List.forall_mem_cons.2 ⟨subd9_0_1117, List.forall_mem_cons.2 ⟨subd9_0_1118, List.forall_mem_cons.2 ⟨subd9_0_1119, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_0_1120 : subd9_0 [4, 1, -5] = true := by decide +kernel
theorem subd9_0_1121 : subd9_0 [4, 1, -4] = true := by decide +kernel
theorem subd9_0_1122 : subd9_0 [4, 1, -3] = true := by decide +kernel
theorem subd9_0_1123 : subd9_0 [4, 1, -2] = true := by decide +kernel
theorem subd9_0_1124 : subd9_0 [4, 1, -1] = true := by decide +kernel
theorem subd9_0_1125 : subd9_0 [4, 1, 0] = true := by decide +kernel
theorem subd9_0_1126 : subd9_0 [4, 1, 1] = true := by decide +kernel
theorem subd9_0_1127 : subd9_0 [4, 1, 2] = true := by decide +kernel
theorem subd9_0_1128 : subd9_0 [4, 1, 3] = true := by decide +kernel
theorem subd9_0_1129 : subd9_0 [4, 1, 4] = true := by decide +kernel
theorem subd9_0_1130 : subd9_0 [4, 1, 5] = true := by decide +kernel
theorem subd9_0_1131 : subd9_0 [4, 1, 6] = true := by decide +kernel
theorem subd9_0_1132 : subd9_0 [4, 1, 7] = true := by decide +kernel
theorem subd9_0_1133 : subd9_0 [4, 2, -6] = true := by decide +kernel
theorem subd9_0_1134 : subd9_0 [4, 2, -5] = true := by decide +kernel
theorem subd9_0_1135 : subd9_0 [4, 2, -4] = true := by decide +kernel
theorem subd9_0_1136 : subd9_0 [4, 2, -3] = true := by decide +kernel
theorem subd9_0_1137 : subd9_0 [4, 2, -2] = true := by decide +kernel
theorem subd9_0_1138 : subd9_0 [4, 2, -1] = true := by decide +kernel
theorem subd9_0_1139 : subd9_0 [4, 2, 0] = true := by decide +kernel
theorem subd9_0_1140 : subd9_0 [4, 2, 1] = true := by decide +kernel
theorem subd9_0_1141 : subd9_0 [4, 2, 2] = true := by decide +kernel
theorem subd9_0_1142 : subd9_0 [4, 2, 3] = true := by decide +kernel
theorem subd9_0_1143 : subd9_0 [4, 2, 4] = true := by decide +kernel
theorem subd9_0_1144 : subd9_0 [4, 2, 5] = true := by decide +kernel
theorem subd9_0_1145 : subd9_0 [4, 2, 6] = true := by decide +kernel
theorem subd9_0_1146 : subd9_0 [4, 2, 7] = true := by decide +kernel
theorem subd9_0_1147 : subd9_0 [4, 3, -6] = true := by decide +kernel
theorem subd9_0_1148 : subd9_0 [4, 3, -5] = true := by decide +kernel
theorem subd9_0_1149 : subd9_0 [4, 3, -4] = true := by decide +kernel
theorem subd9_0_1150 : subd9_0 [4, 3, -3] = true := by decide +kernel
theorem subd9_0_1151 : subd9_0 [4, 3, -2] = true := by decide +kernel
theorem sbd9_0_35 : ∀ q ∈ blkd9_0_35, subd9_0 q = true := by
  unfold blkd9_0_35
  exact List.forall_mem_cons.2 ⟨subd9_0_1120, List.forall_mem_cons.2 ⟨subd9_0_1121, List.forall_mem_cons.2 ⟨subd9_0_1122, List.forall_mem_cons.2 ⟨subd9_0_1123, List.forall_mem_cons.2 ⟨subd9_0_1124, List.forall_mem_cons.2 ⟨subd9_0_1125, List.forall_mem_cons.2 ⟨subd9_0_1126, List.forall_mem_cons.2 ⟨subd9_0_1127, List.forall_mem_cons.2 ⟨subd9_0_1128, List.forall_mem_cons.2 ⟨subd9_0_1129, List.forall_mem_cons.2 ⟨subd9_0_1130, List.forall_mem_cons.2 ⟨subd9_0_1131, List.forall_mem_cons.2 ⟨subd9_0_1132, List.forall_mem_cons.2 ⟨subd9_0_1133, List.forall_mem_cons.2 ⟨subd9_0_1134, List.forall_mem_cons.2 ⟨subd9_0_1135, List.forall_mem_cons.2 ⟨subd9_0_1136, List.forall_mem_cons.2 ⟨subd9_0_1137, List.forall_mem_cons.2 ⟨subd9_0_1138, List.forall_mem_cons.2 ⟨subd9_0_1139, List.forall_mem_cons.2 ⟨subd9_0_1140, List.forall_mem_cons.2 ⟨subd9_0_1141, List.forall_mem_cons.2 ⟨subd9_0_1142, List.forall_mem_cons.2 ⟨subd9_0_1143, List.forall_mem_cons.2 ⟨subd9_0_1144, List.forall_mem_cons.2 ⟨subd9_0_1145, List.forall_mem_cons.2 ⟨subd9_0_1146, List.forall_mem_cons.2 ⟨subd9_0_1147, List.forall_mem_cons.2 ⟨subd9_0_1148, List.forall_mem_cons.2 ⟨subd9_0_1149, List.forall_mem_cons.2 ⟨subd9_0_1150, List.forall_mem_cons.2 ⟨subd9_0_1151, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_0_1152 : subd9_0 [4, 3, -1] = true := by decide +kernel
theorem subd9_0_1153 : subd9_0 [4, 3, 0] = true := by decide +kernel
theorem subd9_0_1154 : subd9_0 [4, 3, 1] = true := by decide +kernel
theorem subd9_0_1155 : subd9_0 [4, 3, 2] = true := by decide +kernel
theorem subd9_0_1156 : subd9_0 [4, 3, 3] = true := by decide +kernel
theorem subd9_0_1157 : subd9_0 [4, 3, 4] = true := by decide +kernel
theorem subd9_0_1158 : subd9_0 [4, 3, 5] = true := by decide +kernel
theorem subd9_0_1159 : subd9_0 [4, 3, 6] = true := by decide +kernel
theorem subd9_0_1160 : subd9_0 [4, 4] = true := by decide +kernel
theorem subd9_0_1161 : subd9_0 [4, 5] = true := by decide +kernel
theorem subd9_0_1162 : subd9_0 [5] = true := by decide +kernel
theorem sbd9_0_36 : ∀ q ∈ blkd9_0_36, subd9_0 q = true := by
  unfold blkd9_0_36
  exact List.forall_mem_cons.2 ⟨subd9_0_1152, List.forall_mem_cons.2 ⟨subd9_0_1153, List.forall_mem_cons.2 ⟨subd9_0_1154, List.forall_mem_cons.2 ⟨subd9_0_1155, List.forall_mem_cons.2 ⟨subd9_0_1156, List.forall_mem_cons.2 ⟨subd9_0_1157, List.forall_mem_cons.2 ⟨subd9_0_1158, List.forall_mem_cons.2 ⟨subd9_0_1159, List.forall_mem_cons.2 ⟨subd9_0_1160, List.forall_mem_cons.2 ⟨subd9_0_1161, List.forall_mem_cons.2 ⟨subd9_0_1162, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd9_1 : ldCheck G d9_1.U d9_1.ms ldd9_1 = true := by decide +kernel
theorem pre_okd9_1 : subPre G cell9 d9_1 = true := by decide +kernel
theorem subd9_1_0 : subd9_1 [-6] = true := by decide +kernel
theorem subd9_1_1 : subd9_1 [-5, -5] = true := by decide +kernel
theorem subd9_1_2 : subd9_1 [-5, -4] = true := by decide +kernel
theorem subd9_1_3 : subd9_1 [-5, -3] = true := by decide +kernel
theorem subd9_1_4 : subd9_1 [-5, -2] = true := by decide +kernel
theorem subd9_1_5 : subd9_1 [-5, -1] = true := by decide +kernel
theorem subd9_1_6 : subd9_1 [-5, 0] = true := by decide +kernel
theorem subd9_1_7 : subd9_1 [-5, 1] = true := by decide +kernel
theorem subd9_1_8 : subd9_1 [-5, 2] = true := by decide +kernel
theorem subd9_1_9 : subd9_1 [-4, -6] = true := by decide +kernel
theorem subd9_1_10 : subd9_1 [-4, -5] = true := by decide +kernel
theorem subd9_1_11 : subd9_1 [-4, -4] = true := by decide +kernel
theorem subd9_1_12 : subd9_1 [-4, -3] = true := by decide +kernel
theorem subd9_1_13 : subd9_1 [-4, -2] = true := by decide +kernel
theorem subd9_1_14 : subd9_1 [-4, -1] = true := by decide +kernel
theorem subd9_1_15 : subd9_1 [-4, 0] = true := by decide +kernel
theorem subd9_1_16 : subd9_1 [-4, 1] = true := by decide +kernel
theorem subd9_1_17 : subd9_1 [-4, 2] = true := by decide +kernel
theorem subd9_1_18 : subd9_1 [-4, 3] = true := by decide +kernel
theorem subd9_1_19 : subd9_1 [-3, -6] = true := by decide +kernel
theorem subd9_1_20 : subd9_1 [-3, -5] = true := by decide +kernel
theorem subd9_1_21 : subd9_1 [-3, -4] = true := by decide +kernel
theorem subd9_1_22 : subd9_1 [-3, -3] = true := by decide +kernel
theorem subd9_1_23 : subd9_1 [-3, -2] = true := by decide +kernel
theorem subd9_1_24 : subd9_1 [-3, -1] = true := by decide +kernel
theorem subd9_1_25 : subd9_1 [-3, 0] = true := by decide +kernel
theorem subd9_1_26 : subd9_1 [-3, 1] = true := by decide +kernel
theorem subd9_1_27 : subd9_1 [-3, 2] = true := by decide +kernel
theorem subd9_1_28 : subd9_1 [-3, 3] = true := by decide +kernel
theorem subd9_1_29 : subd9_1 [-3, 4] = true := by decide +kernel
theorem subd9_1_30 : subd9_1 [-2, -6] = true := by decide +kernel
theorem subd9_1_31 : subd9_1 [-2, -5] = true := by decide +kernel
theorem sbd9_1_0 : ∀ q ∈ blkd9_1_0, subd9_1 q = true := by
  unfold blkd9_1_0
  exact List.forall_mem_cons.2 ⟨subd9_1_0, List.forall_mem_cons.2 ⟨subd9_1_1, List.forall_mem_cons.2 ⟨subd9_1_2, List.forall_mem_cons.2 ⟨subd9_1_3, List.forall_mem_cons.2 ⟨subd9_1_4, List.forall_mem_cons.2 ⟨subd9_1_5, List.forall_mem_cons.2 ⟨subd9_1_6, List.forall_mem_cons.2 ⟨subd9_1_7, List.forall_mem_cons.2 ⟨subd9_1_8, List.forall_mem_cons.2 ⟨subd9_1_9, List.forall_mem_cons.2 ⟨subd9_1_10, List.forall_mem_cons.2 ⟨subd9_1_11, List.forall_mem_cons.2 ⟨subd9_1_12, List.forall_mem_cons.2 ⟨subd9_1_13, List.forall_mem_cons.2 ⟨subd9_1_14, List.forall_mem_cons.2 ⟨subd9_1_15, List.forall_mem_cons.2 ⟨subd9_1_16, List.forall_mem_cons.2 ⟨subd9_1_17, List.forall_mem_cons.2 ⟨subd9_1_18, List.forall_mem_cons.2 ⟨subd9_1_19, List.forall_mem_cons.2 ⟨subd9_1_20, List.forall_mem_cons.2 ⟨subd9_1_21, List.forall_mem_cons.2 ⟨subd9_1_22, List.forall_mem_cons.2 ⟨subd9_1_23, List.forall_mem_cons.2 ⟨subd9_1_24, List.forall_mem_cons.2 ⟨subd9_1_25, List.forall_mem_cons.2 ⟨subd9_1_26, List.forall_mem_cons.2 ⟨subd9_1_27, List.forall_mem_cons.2 ⟨subd9_1_28, List.forall_mem_cons.2 ⟨subd9_1_29, List.forall_mem_cons.2 ⟨subd9_1_30, List.forall_mem_cons.2 ⟨subd9_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C131
