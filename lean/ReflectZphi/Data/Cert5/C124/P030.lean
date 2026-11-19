import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_14_928 : subd6_14 [3, -2, 2] = true := by decide +kernel
theorem subd6_14_929 : subd6_14 [3, -2, 3] = true := by decide +kernel
theorem subd6_14_930 : subd6_14 [3, -2, 4] = true := by decide +kernel
theorem subd6_14_931 : subd6_14 [3, -2, 5] = true := by decide +kernel
theorem subd6_14_932 : subd6_14 [3, -2, 6] = true := by decide +kernel
theorem subd6_14_933 : subd6_14 [3, -2, 7] = true := by decide +kernel
theorem subd6_14_934 : subd6_14 [3, -1, -10] = true := by decide +kernel
theorem subd6_14_935 : subd6_14 [3, -1, -9] = true := by decide +kernel
theorem subd6_14_936 : subd6_14 [3, -1, -8] = true := by decide +kernel
theorem subd6_14_937 : subd6_14 [3, -1, -7] = true := by decide +kernel
theorem subd6_14_938 : subd6_14 [3, -1, -6] = true := by decide +kernel
theorem subd6_14_939 : subd6_14 [3, -1, -5] = true := by decide +kernel
theorem subd6_14_940 : subd6_14 [3, -1, -4] = true := by decide +kernel
theorem subd6_14_941 : subd6_14 [3, -1, -3] = true := by decide +kernel
theorem subd6_14_942 : subd6_14 [3, -1, -2] = true := by decide +kernel
theorem subd6_14_943 : subd6_14 [3, -1, -1] = true := by decide +kernel
theorem subd6_14_944 : subd6_14 [3, -1, 0] = true := by decide +kernel
theorem subd6_14_945 : subd6_14 [3, -1, 1] = true := by decide +kernel
theorem subd6_14_946 : subd6_14 [3, -1, 2] = true := by decide +kernel
theorem subd6_14_947 : subd6_14 [3, -1, 3] = true := by decide +kernel
theorem subd6_14_948 : subd6_14 [3, -1, 4] = true := by decide +kernel
theorem subd6_14_949 : subd6_14 [3, -1, 5] = true := by decide +kernel
theorem subd6_14_950 : subd6_14 [3, -1, 6] = true := by decide +kernel
theorem subd6_14_951 : subd6_14 [3, -1, 7] = true := by decide +kernel
theorem subd6_14_952 : subd6_14 [3, -1, 8] = true := by decide +kernel
theorem subd6_14_953 : subd6_14 [3, 0, -10] = true := by decide +kernel
theorem subd6_14_954 : subd6_14 [3, 0, -9] = true := by decide +kernel
theorem subd6_14_955 : subd6_14 [3, 0, -8] = true := by decide +kernel
theorem subd6_14_956 : subd6_14 [3, 0, -7] = true := by decide +kernel
theorem subd6_14_957 : subd6_14 [3, 0, -6] = true := by decide +kernel
theorem subd6_14_958 : subd6_14 [3, 0, -5] = true := by decide +kernel
theorem subd6_14_959 : subd6_14 [3, 0, -4] = true := by decide +kernel
theorem sbd6_14_29 : ∀ q ∈ blkd6_14_29, subd6_14 q = true := by
  unfold blkd6_14_29
  exact List.forall_mem_cons.2 ⟨subd6_14_928, List.forall_mem_cons.2 ⟨subd6_14_929, List.forall_mem_cons.2 ⟨subd6_14_930, List.forall_mem_cons.2 ⟨subd6_14_931, List.forall_mem_cons.2 ⟨subd6_14_932, List.forall_mem_cons.2 ⟨subd6_14_933, List.forall_mem_cons.2 ⟨subd6_14_934, List.forall_mem_cons.2 ⟨subd6_14_935, List.forall_mem_cons.2 ⟨subd6_14_936, List.forall_mem_cons.2 ⟨subd6_14_937, List.forall_mem_cons.2 ⟨subd6_14_938, List.forall_mem_cons.2 ⟨subd6_14_939, List.forall_mem_cons.2 ⟨subd6_14_940, List.forall_mem_cons.2 ⟨subd6_14_941, List.forall_mem_cons.2 ⟨subd6_14_942, List.forall_mem_cons.2 ⟨subd6_14_943, List.forall_mem_cons.2 ⟨subd6_14_944, List.forall_mem_cons.2 ⟨subd6_14_945, List.forall_mem_cons.2 ⟨subd6_14_946, List.forall_mem_cons.2 ⟨subd6_14_947, List.forall_mem_cons.2 ⟨subd6_14_948, List.forall_mem_cons.2 ⟨subd6_14_949, List.forall_mem_cons.2 ⟨subd6_14_950, List.forall_mem_cons.2 ⟨subd6_14_951, List.forall_mem_cons.2 ⟨subd6_14_952, List.forall_mem_cons.2 ⟨subd6_14_953, List.forall_mem_cons.2 ⟨subd6_14_954, List.forall_mem_cons.2 ⟨subd6_14_955, List.forall_mem_cons.2 ⟨subd6_14_956, List.forall_mem_cons.2 ⟨subd6_14_957, List.forall_mem_cons.2 ⟨subd6_14_958, List.forall_mem_cons.2 ⟨subd6_14_959, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_14_960 : subd6_14 [3, 0, -3] = true := by decide +kernel
theorem subd6_14_961 : subd6_14 [3, 0, -2] = true := by decide +kernel
theorem subd6_14_962 : subd6_14 [3, 0, -1] = true := by decide +kernel
theorem subd6_14_963 : subd6_14 [3, 0, 0] = true := by decide +kernel
theorem subd6_14_964 : subd6_14 [3, 0, 1] = true := by decide +kernel
theorem subd6_14_965 : subd6_14 [3, 0, 2] = true := by decide +kernel
theorem subd6_14_966 : subd6_14 [3, 0, 3] = true := by decide +kernel
theorem subd6_14_967 : subd6_14 [3, 0, 4] = true := by decide +kernel
theorem subd6_14_968 : subd6_14 [3, 0, 5] = true := by decide +kernel
theorem subd6_14_969 : subd6_14 [3, 0, 6] = true := by decide +kernel
theorem subd6_14_970 : subd6_14 [3, 0, 7] = true := by decide +kernel
theorem subd6_14_971 : subd6_14 [3, 0, 8] = true := by decide +kernel
theorem subd6_14_972 : subd6_14 [3, 0, 9] = true := by decide +kernel
theorem subd6_14_973 : subd6_14 [3, 1, -9] = true := by decide +kernel
theorem subd6_14_974 : subd6_14 [3, 1, -8] = true := by decide +kernel
theorem subd6_14_975 : subd6_14 [3, 1, -7] = true := by decide +kernel
theorem subd6_14_976 : subd6_14 [3, 1, -6] = true := by decide +kernel
theorem subd6_14_977 : subd6_14 [3, 1, -5] = true := by decide +kernel
theorem subd6_14_978 : subd6_14 [3, 1, -4] = true := by decide +kernel
theorem subd6_14_979 : subd6_14 [3, 1, -3] = true := by decide +kernel
theorem subd6_14_980 : subd6_14 [3, 1, -2] = true := by decide +kernel
theorem subd6_14_981 : subd6_14 [3, 1, -1] = true := by decide +kernel
theorem subd6_14_982 : subd6_14 [3, 1, 0] = true := by decide +kernel
theorem subd6_14_983 : subd6_14 [3, 1, 1] = true := by decide +kernel
theorem subd6_14_984 : subd6_14 [3, 1, 2] = true := by decide +kernel
theorem subd6_14_985 : subd6_14 [3, 1, 3] = true := by decide +kernel
theorem subd6_14_986 : subd6_14 [3, 1, 4] = true := by decide +kernel
theorem subd6_14_987 : subd6_14 [3, 1, 5] = true := by decide +kernel
theorem subd6_14_988 : subd6_14 [3, 1, 6] = true := by decide +kernel
theorem subd6_14_989 : subd6_14 [3, 1, 7] = true := by decide +kernel
theorem subd6_14_990 : subd6_14 [3, 1, 8] = true := by decide +kernel
theorem subd6_14_991 : subd6_14 [3, 1, 9] = true := by decide +kernel
theorem sbd6_14_30 : ∀ q ∈ blkd6_14_30, subd6_14 q = true := by
  unfold blkd6_14_30
  exact List.forall_mem_cons.2 ⟨subd6_14_960, List.forall_mem_cons.2 ⟨subd6_14_961, List.forall_mem_cons.2 ⟨subd6_14_962, List.forall_mem_cons.2 ⟨subd6_14_963, List.forall_mem_cons.2 ⟨subd6_14_964, List.forall_mem_cons.2 ⟨subd6_14_965, List.forall_mem_cons.2 ⟨subd6_14_966, List.forall_mem_cons.2 ⟨subd6_14_967, List.forall_mem_cons.2 ⟨subd6_14_968, List.forall_mem_cons.2 ⟨subd6_14_969, List.forall_mem_cons.2 ⟨subd6_14_970, List.forall_mem_cons.2 ⟨subd6_14_971, List.forall_mem_cons.2 ⟨subd6_14_972, List.forall_mem_cons.2 ⟨subd6_14_973, List.forall_mem_cons.2 ⟨subd6_14_974, List.forall_mem_cons.2 ⟨subd6_14_975, List.forall_mem_cons.2 ⟨subd6_14_976, List.forall_mem_cons.2 ⟨subd6_14_977, List.forall_mem_cons.2 ⟨subd6_14_978, List.forall_mem_cons.2 ⟨subd6_14_979, List.forall_mem_cons.2 ⟨subd6_14_980, List.forall_mem_cons.2 ⟨subd6_14_981, List.forall_mem_cons.2 ⟨subd6_14_982, List.forall_mem_cons.2 ⟨subd6_14_983, List.forall_mem_cons.2 ⟨subd6_14_984, List.forall_mem_cons.2 ⟨subd6_14_985, List.forall_mem_cons.2 ⟨subd6_14_986, List.forall_mem_cons.2 ⟨subd6_14_987, List.forall_mem_cons.2 ⟨subd6_14_988, List.forall_mem_cons.2 ⟨subd6_14_989, List.forall_mem_cons.2 ⟨subd6_14_990, List.forall_mem_cons.2 ⟨subd6_14_991, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_14_992 : subd6_14 [3, 2, -8] = true := by decide +kernel
theorem subd6_14_993 : subd6_14 [3, 2, -7] = true := by decide +kernel
theorem subd6_14_994 : subd6_14 [3, 2, -6] = true := by decide +kernel
theorem subd6_14_995 : subd6_14 [3, 2, -5] = true := by decide +kernel
theorem subd6_14_996 : subd6_14 [3, 2, -4] = true := by decide +kernel
theorem subd6_14_997 : subd6_14 [3, 2, -3] = true := by decide +kernel
theorem subd6_14_998 : subd6_14 [3, 2, -2] = true := by decide +kernel
theorem subd6_14_999 : subd6_14 [3, 2, -1] = true := by decide +kernel
theorem subd6_14_1000 : subd6_14 [3, 2, 0] = true := by decide +kernel
theorem subd6_14_1001 : subd6_14 [3, 2, 1] = true := by decide +kernel
theorem subd6_14_1002 : subd6_14 [3, 2, 2] = true := by decide +kernel
theorem subd6_14_1003 : subd6_14 [3, 2, 3] = true := by decide +kernel
theorem subd6_14_1004 : subd6_14 [3, 2, 4] = true := by decide +kernel
theorem subd6_14_1005 : subd6_14 [3, 2, 5] = true := by decide +kernel
theorem subd6_14_1006 : subd6_14 [3, 2, 6] = true := by decide +kernel
theorem subd6_14_1007 : subd6_14 [3, 2, 7] = true := by decide +kernel
theorem subd6_14_1008 : subd6_14 [3, 2, 8] = true := by decide +kernel
theorem subd6_14_1009 : subd6_14 [3, 3] = true := by decide +kernel
theorem subd6_14_1010 : subd6_14 [4, -3] = true := by decide +kernel
theorem subd6_14_1011 : subd6_14 [4, -2] = true := by decide +kernel
theorem subd6_14_1012 : subd6_14 [4, -1] = true := by decide +kernel
theorem subd6_14_1013 : subd6_14 [4, 0, -7] = true := by decide +kernel
theorem subd6_14_1014 : subd6_14 [4, 0, -6] = true := by decide +kernel
theorem subd6_14_1015 : subd6_14 [4, 0, -5] = true := by decide +kernel
theorem subd6_14_1016 : subd6_14 [4, 0, -4] = true := by decide +kernel
theorem subd6_14_1017 : subd6_14 [4, 0, -3] = true := by decide +kernel
theorem subd6_14_1018 : subd6_14 [4, 0, -2] = true := by decide +kernel
theorem subd6_14_1019 : subd6_14 [4, 0, -1] = true := by decide +kernel
theorem subd6_14_1020 : subd6_14 [4, 0, 0] = true := by decide +kernel
theorem subd6_14_1021 : subd6_14 [4, 0, 1] = true := by decide +kernel
theorem subd6_14_1022 : subd6_14 [4, 0, 2] = true := by decide +kernel
theorem subd6_14_1023 : subd6_14 [4, 0, 3] = true := by decide +kernel
theorem sbd6_14_31 : ∀ q ∈ blkd6_14_31, subd6_14 q = true := by
  unfold blkd6_14_31
  exact List.forall_mem_cons.2 ⟨subd6_14_992, List.forall_mem_cons.2 ⟨subd6_14_993, List.forall_mem_cons.2 ⟨subd6_14_994, List.forall_mem_cons.2 ⟨subd6_14_995, List.forall_mem_cons.2 ⟨subd6_14_996, List.forall_mem_cons.2 ⟨subd6_14_997, List.forall_mem_cons.2 ⟨subd6_14_998, List.forall_mem_cons.2 ⟨subd6_14_999, List.forall_mem_cons.2 ⟨subd6_14_1000, List.forall_mem_cons.2 ⟨subd6_14_1001, List.forall_mem_cons.2 ⟨subd6_14_1002, List.forall_mem_cons.2 ⟨subd6_14_1003, List.forall_mem_cons.2 ⟨subd6_14_1004, List.forall_mem_cons.2 ⟨subd6_14_1005, List.forall_mem_cons.2 ⟨subd6_14_1006, List.forall_mem_cons.2 ⟨subd6_14_1007, List.forall_mem_cons.2 ⟨subd6_14_1008, List.forall_mem_cons.2 ⟨subd6_14_1009, List.forall_mem_cons.2 ⟨subd6_14_1010, List.forall_mem_cons.2 ⟨subd6_14_1011, List.forall_mem_cons.2 ⟨subd6_14_1012, List.forall_mem_cons.2 ⟨subd6_14_1013, List.forall_mem_cons.2 ⟨subd6_14_1014, List.forall_mem_cons.2 ⟨subd6_14_1015, List.forall_mem_cons.2 ⟨subd6_14_1016, List.forall_mem_cons.2 ⟨subd6_14_1017, List.forall_mem_cons.2 ⟨subd6_14_1018, List.forall_mem_cons.2 ⟨subd6_14_1019, List.forall_mem_cons.2 ⟨subd6_14_1020, List.forall_mem_cons.2 ⟨subd6_14_1021, List.forall_mem_cons.2 ⟨subd6_14_1022, List.forall_mem_cons.2 ⟨subd6_14_1023, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_14_1024 : subd6_14 [4, 0, 4] = true := by decide +kernel
theorem subd6_14_1025 : subd6_14 [4, 0, 5] = true := by decide +kernel
theorem subd6_14_1026 : subd6_14 [4, 0, 6] = true := by decide +kernel
theorem subd6_14_1027 : subd6_14 [4, 1] = true := by decide +kernel
theorem subd6_14_1028 : subd6_14 [4, 2] = true := by decide +kernel
theorem sbd6_14_32 : ∀ q ∈ blkd6_14_32, subd6_14 q = true := by
  unfold blkd6_14_32
  exact List.forall_mem_cons.2 ⟨subd6_14_1024, List.forall_mem_cons.2 ⟨subd6_14_1025, List.forall_mem_cons.2 ⟨subd6_14_1026, List.forall_mem_cons.2 ⟨subd6_14_1027, List.forall_mem_cons.2 ⟨subd6_14_1028, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd7_0 : ldCheck G d7_0.U d7_0.ms ldd7_0 = true := by decide +kernel
theorem pre_okd7_0 : subPre G cell7 d7_0 = true := by decide +kernel
theorem subd7_0_0 : subd7_0 [-2] = true := by decide +kernel
theorem subd7_0_1 : subd7_0 [-1, -3] = true := by decide +kernel
theorem subd7_0_2 : subd7_0 [-1, -2] = true := by decide +kernel
theorem subd7_0_3 : subd7_0 [-1, -1] = true := by decide +kernel
theorem subd7_0_4 : subd7_0 [-1, 0] = true := by decide +kernel
theorem subd7_0_5 : subd7_0 [-1, 1] = true := by decide +kernel
theorem subd7_0_6 : subd7_0 [-1, 2] = true := by decide +kernel
theorem subd7_0_7 : subd7_0 [-1, 3] = true := by decide +kernel
theorem subd7_0_8 : subd7_0 [0, -4] = true := by decide +kernel
theorem subd7_0_9 : subd7_0 [0, -3] = true := by decide +kernel
theorem subd7_0_10 : subd7_0 [0, -2] = true := by decide +kernel
theorem subd7_0_11 : subd7_0 [0, -1] = true := by decide +kernel
theorem subd7_0_12 : subd7_0 [0, 0] = true := by decide +kernel
theorem subd7_0_13 : subd7_0 [0, 1] = true := by decide +kernel
theorem subd7_0_14 : subd7_0 [0, 2] = true := by decide +kernel
theorem subd7_0_15 : subd7_0 [0, 3] = true := by decide +kernel
theorem subd7_0_16 : subd7_0 [1, -4] = true := by decide +kernel
theorem subd7_0_17 : subd7_0 [1, -3] = true := by decide +kernel
theorem subd7_0_18 : subd7_0 [1, -2] = true := by decide +kernel
theorem subd7_0_19 : subd7_0 [1, -1] = true := by decide +kernel
theorem subd7_0_20 : subd7_0 [1, 0] = true := by decide +kernel
theorem subd7_0_21 : subd7_0 [1, 1] = true := by decide +kernel
theorem subd7_0_22 : subd7_0 [1, 2] = true := by decide +kernel
theorem subd7_0_23 : subd7_0 [2] = true := by decide +kernel
theorem sbd7_0_0 : ∀ q ∈ blkd7_0_0, subd7_0 q = true := by
  unfold blkd7_0_0
  exact List.forall_mem_cons.2 ⟨subd7_0_0, List.forall_mem_cons.2 ⟨subd7_0_1, List.forall_mem_cons.2 ⟨subd7_0_2, List.forall_mem_cons.2 ⟨subd7_0_3, List.forall_mem_cons.2 ⟨subd7_0_4, List.forall_mem_cons.2 ⟨subd7_0_5, List.forall_mem_cons.2 ⟨subd7_0_6, List.forall_mem_cons.2 ⟨subd7_0_7, List.forall_mem_cons.2 ⟨subd7_0_8, List.forall_mem_cons.2 ⟨subd7_0_9, List.forall_mem_cons.2 ⟨subd7_0_10, List.forall_mem_cons.2 ⟨subd7_0_11, List.forall_mem_cons.2 ⟨subd7_0_12, List.forall_mem_cons.2 ⟨subd7_0_13, List.forall_mem_cons.2 ⟨subd7_0_14, List.forall_mem_cons.2 ⟨subd7_0_15, List.forall_mem_cons.2 ⟨subd7_0_16, List.forall_mem_cons.2 ⟨subd7_0_17, List.forall_mem_cons.2 ⟨subd7_0_18, List.forall_mem_cons.2 ⟨subd7_0_19, List.forall_mem_cons.2 ⟨subd7_0_20, List.forall_mem_cons.2 ⟨subd7_0_21, List.forall_mem_cons.2 ⟨subd7_0_22, List.forall_mem_cons.2 ⟨subd7_0_23, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_1 : ldCheck G d7_1.U d7_1.ms ldd7_1 = true := by decide +kernel
theorem pre_okd7_1 : subPre G cell7 d7_1 = true := by decide +kernel
theorem subd7_1_0 : subd7_1 [-3] = true := by decide +kernel
theorem subd7_1_1 : subd7_1 [-2, -4] = true := by decide +kernel
theorem subd7_1_2 : subd7_1 [-2, -3] = true := by decide +kernel
theorem subd7_1_3 : subd7_1 [-2, -2] = true := by decide +kernel
theorem subd7_1_4 : subd7_1 [-2, -1] = true := by decide +kernel
theorem subd7_1_5 : subd7_1 [-2, 0] = true := by decide +kernel
theorem subd7_1_6 : subd7_1 [-2, 1] = true := by decide +kernel
theorem subd7_1_7 : subd7_1 [-2, 2] = true := by decide +kernel
theorem subd7_1_8 : subd7_1 [-1, -4] = true := by decide +kernel
theorem subd7_1_9 : subd7_1 [-1, -3] = true := by decide +kernel
theorem subd7_1_10 : subd7_1 [-1, -2] = true := by decide +kernel
theorem subd7_1_11 : subd7_1 [-1, -1] = true := by decide +kernel
theorem subd7_1_12 : subd7_1 [-1, 0] = true := by decide +kernel
theorem subd7_1_13 : subd7_1 [-1, 1] = true := by decide +kernel
theorem subd7_1_14 : subd7_1 [-1, 2] = true := by decide +kernel
theorem subd7_1_15 : subd7_1 [-1, 3] = true := by decide +kernel
theorem subd7_1_16 : subd7_1 [0, -4] = true := by decide +kernel
theorem subd7_1_17 : subd7_1 [0, -3] = true := by decide +kernel
theorem subd7_1_18 : subd7_1 [0, -2] = true := by decide +kernel
theorem subd7_1_19 : subd7_1 [0, -1] = true := by decide +kernel
theorem subd7_1_20 : subd7_1 [0, 0] = true := by decide +kernel
theorem subd7_1_21 : subd7_1 [0, 1] = true := by decide +kernel
theorem subd7_1_22 : subd7_1 [0, 2] = true := by decide +kernel
theorem subd7_1_23 : subd7_1 [0, 3] = true := by decide +kernel
theorem subd7_1_24 : subd7_1 [1, -4] = true := by decide +kernel
theorem subd7_1_25 : subd7_1 [1, -3] = true := by decide +kernel
theorem subd7_1_26 : subd7_1 [1, -2] = true := by decide +kernel
theorem subd7_1_27 : subd7_1 [1, -1] = true := by decide +kernel
theorem subd7_1_28 : subd7_1 [1, 0] = true := by decide +kernel
theorem subd7_1_29 : subd7_1 [1, 1] = true := by decide +kernel
theorem subd7_1_30 : subd7_1 [1, 2] = true := by decide +kernel
theorem subd7_1_31 : subd7_1 [1, 3] = true := by decide +kernel
theorem sbd7_1_0 : ∀ q ∈ blkd7_1_0, subd7_1 q = true := by
  unfold blkd7_1_0
  exact List.forall_mem_cons.2 ⟨subd7_1_0, List.forall_mem_cons.2 ⟨subd7_1_1, List.forall_mem_cons.2 ⟨subd7_1_2, List.forall_mem_cons.2 ⟨subd7_1_3, List.forall_mem_cons.2 ⟨subd7_1_4, List.forall_mem_cons.2 ⟨subd7_1_5, List.forall_mem_cons.2 ⟨subd7_1_6, List.forall_mem_cons.2 ⟨subd7_1_7, List.forall_mem_cons.2 ⟨subd7_1_8, List.forall_mem_cons.2 ⟨subd7_1_9, List.forall_mem_cons.2 ⟨subd7_1_10, List.forall_mem_cons.2 ⟨subd7_1_11, List.forall_mem_cons.2 ⟨subd7_1_12, List.forall_mem_cons.2 ⟨subd7_1_13, List.forall_mem_cons.2 ⟨subd7_1_14, List.forall_mem_cons.2 ⟨subd7_1_15, List.forall_mem_cons.2 ⟨subd7_1_16, List.forall_mem_cons.2 ⟨subd7_1_17, List.forall_mem_cons.2 ⟨subd7_1_18, List.forall_mem_cons.2 ⟨subd7_1_19, List.forall_mem_cons.2 ⟨subd7_1_20, List.forall_mem_cons.2 ⟨subd7_1_21, List.forall_mem_cons.2 ⟨subd7_1_22, List.forall_mem_cons.2 ⟨subd7_1_23, List.forall_mem_cons.2 ⟨subd7_1_24, List.forall_mem_cons.2 ⟨subd7_1_25, List.forall_mem_cons.2 ⟨subd7_1_26, List.forall_mem_cons.2 ⟨subd7_1_27, List.forall_mem_cons.2 ⟨subd7_1_28, List.forall_mem_cons.2 ⟨subd7_1_29, List.forall_mem_cons.2 ⟨subd7_1_30, List.forall_mem_cons.2 ⟨subd7_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_32 : subd7_1 [2, -3] = true := by decide +kernel
theorem subd7_1_33 : subd7_1 [2, -2] = true := by decide +kernel
theorem subd7_1_34 : subd7_1 [2, -1] = true := by decide +kernel
theorem subd7_1_35 : subd7_1 [2, 0] = true := by decide +kernel
theorem subd7_1_36 : subd7_1 [2, 1] = true := by decide +kernel
theorem subd7_1_37 : subd7_1 [2, 2] = true := by decide +kernel
theorem subd7_1_38 : subd7_1 [2, 3] = true := by decide +kernel
theorem subd7_1_39 : subd7_1 [3] = true := by decide +kernel
theorem sbd7_1_1 : ∀ q ∈ blkd7_1_1, subd7_1 q = true := by
  unfold blkd7_1_1
  exact List.forall_mem_cons.2 ⟨subd7_1_32, List.forall_mem_cons.2 ⟨subd7_1_33, List.forall_mem_cons.2 ⟨subd7_1_34, List.forall_mem_cons.2 ⟨subd7_1_35, List.forall_mem_cons.2 ⟨subd7_1_36, List.forall_mem_cons.2 ⟨subd7_1_37, List.forall_mem_cons.2 ⟨subd7_1_38, List.forall_mem_cons.2 ⟨subd7_1_39, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_2 : ldCheck G d7_2.U d7_2.ms ldd7_2 = true := by decide +kernel
theorem pre_okd7_2 : subPre G cell7 d7_2 = true := by decide +kernel
theorem subd7_2_0 : subd7_2 [-3] = true := by decide +kernel
theorem subd7_2_1 : subd7_2 [-2] = true := by decide +kernel
theorem subd7_2_2 : subd7_2 [-1, -4] = true := by decide +kernel
theorem subd7_2_3 : subd7_2 [-1, -3] = true := by decide +kernel
theorem subd7_2_4 : subd7_2 [-1, -2] = true := by decide +kernel
theorem subd7_2_5 : subd7_2 [-1, -1] = true := by decide +kernel
theorem subd7_2_6 : subd7_2 [-1, 0] = true := by decide +kernel
theorem subd7_2_7 : subd7_2 [-1, 1] = true := by decide +kernel
theorem subd7_2_8 : subd7_2 [-1, 2] = true := by decide +kernel
theorem subd7_2_9 : subd7_2 [0, -4] = true := by decide +kernel
theorem subd7_2_10 : subd7_2 [0, -3] = true := by decide +kernel
theorem subd7_2_11 : subd7_2 [0, -2] = true := by decide +kernel
theorem subd7_2_12 : subd7_2 [0, -1] = true := by decide +kernel
theorem subd7_2_13 : subd7_2 [0, 0] = true := by decide +kernel
theorem subd7_2_14 : subd7_2 [0, 1] = true := by decide +kernel
theorem subd7_2_15 : subd7_2 [0, 2] = true := by decide +kernel
theorem subd7_2_16 : subd7_2 [0, 3] = true := by decide +kernel
theorem subd7_2_17 : subd7_2 [1, -3] = true := by decide +kernel
theorem subd7_2_18 : subd7_2 [1, -2] = true := by decide +kernel
theorem subd7_2_19 : subd7_2 [1, -1] = true := by decide +kernel
theorem subd7_2_20 : subd7_2 [1, 0] = true := by decide +kernel
theorem subd7_2_21 : subd7_2 [1, 1] = true := by decide +kernel
theorem subd7_2_22 : subd7_2 [1, 2] = true := by decide +kernel
theorem subd7_2_23 : subd7_2 [1, 3] = true := by decide +kernel
theorem subd7_2_24 : subd7_2 [2] = true := by decide +kernel
theorem subd7_2_25 : subd7_2 [3] = true := by decide +kernel
theorem sbd7_2_0 : ∀ q ∈ blkd7_2_0, subd7_2 q = true := by
  unfold blkd7_2_0
  exact List.forall_mem_cons.2 ⟨subd7_2_0, List.forall_mem_cons.2 ⟨subd7_2_1, List.forall_mem_cons.2 ⟨subd7_2_2, List.forall_mem_cons.2 ⟨subd7_2_3, List.forall_mem_cons.2 ⟨subd7_2_4, List.forall_mem_cons.2 ⟨subd7_2_5, List.forall_mem_cons.2 ⟨subd7_2_6, List.forall_mem_cons.2 ⟨subd7_2_7, List.forall_mem_cons.2 ⟨subd7_2_8, List.forall_mem_cons.2 ⟨subd7_2_9, List.forall_mem_cons.2 ⟨subd7_2_10, List.forall_mem_cons.2 ⟨subd7_2_11, List.forall_mem_cons.2 ⟨subd7_2_12, List.forall_mem_cons.2 ⟨subd7_2_13, List.forall_mem_cons.2 ⟨subd7_2_14, List.forall_mem_cons.2 ⟨subd7_2_15, List.forall_mem_cons.2 ⟨subd7_2_16, List.forall_mem_cons.2 ⟨subd7_2_17, List.forall_mem_cons.2 ⟨subd7_2_18, List.forall_mem_cons.2 ⟨subd7_2_19, List.forall_mem_cons.2 ⟨subd7_2_20, List.forall_mem_cons.2 ⟨subd7_2_21, List.forall_mem_cons.2 ⟨subd7_2_22, List.forall_mem_cons.2 ⟨subd7_2_23, List.forall_mem_cons.2 ⟨subd7_2_24, List.forall_mem_cons.2 ⟨subd7_2_25, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C124
