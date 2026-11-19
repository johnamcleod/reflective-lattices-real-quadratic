import ReflectZphi.Data.Cert5.C121.Base

namespace ReflectZphi.Data.Cert5.C121

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_2_960 : subd9_2 [3, 2, -5] = true := by decide +kernel
theorem subd9_2_961 : subd9_2 [3, 2, -4] = true := by decide +kernel
theorem subd9_2_962 : subd9_2 [3, 2, -3] = true := by decide +kernel
theorem subd9_2_963 : subd9_2 [3, 2, -2] = true := by decide +kernel
theorem subd9_2_964 : subd9_2 [3, 2, -1] = true := by decide +kernel
theorem subd9_2_965 : subd9_2 [3, 2, 0] = true := by decide +kernel
theorem subd9_2_966 : subd9_2 [3, 2, 1] = true := by decide +kernel
theorem subd9_2_967 : subd9_2 [3, 2, 2] = true := by decide +kernel
theorem subd9_2_968 : subd9_2 [3, 2, 3] = true := by decide +kernel
theorem subd9_2_969 : subd9_2 [3, 2, 4] = true := by decide +kernel
theorem subd9_2_970 : subd9_2 [3, 2, 5] = true := by decide +kernel
theorem subd9_2_971 : subd9_2 [3, 2, 6] = true := by decide +kernel
theorem subd9_2_972 : subd9_2 [3, 2, 7] = true := by decide +kernel
theorem subd9_2_973 : subd9_2 [3, 3] = true := by decide +kernel
theorem subd9_2_974 : subd9_2 [3, 4] = true := by decide +kernel
theorem subd9_2_975 : subd9_2 [3, 5] = true := by decide +kernel
theorem subd9_2_976 : subd9_2 [3, 6] = true := by decide +kernel
theorem subd9_2_977 : subd9_2 [3, 7] = true := by decide +kernel
theorem subd9_2_978 : subd9_2 [4, -9] = true := by decide +kernel
theorem subd9_2_979 : subd9_2 [4, -8] = true := by decide +kernel
theorem subd9_2_980 : subd9_2 [4, -7] = true := by decide +kernel
theorem subd9_2_981 : subd9_2 [4, -6] = true := by decide +kernel
theorem subd9_2_982 : subd9_2 [4, -5] = true := by decide +kernel
theorem subd9_2_983 : subd9_2 [4, -4] = true := by decide +kernel
theorem subd9_2_984 : subd9_2 [4, -3] = true := by decide +kernel
theorem subd9_2_985 : subd9_2 [4, -2, -6] = true := by decide +kernel
theorem subd9_2_986 : subd9_2 [4, -2, -5] = true := by decide +kernel
theorem subd9_2_987 : subd9_2 [4, -2, -4] = true := by decide +kernel
theorem subd9_2_988 : subd9_2 [4, -2, -3] = true := by decide +kernel
theorem subd9_2_989 : subd9_2 [4, -2, -2] = true := by decide +kernel
theorem subd9_2_990 : subd9_2 [4, -2, -1] = true := by decide +kernel
theorem subd9_2_991 : subd9_2 [4, -2, 0] = true := by decide +kernel
theorem sbd9_2_30 : ∀ q ∈ blkd9_2_30, subd9_2 q = true := by
  unfold blkd9_2_30
  exact List.forall_mem_cons.2 ⟨subd9_2_960, List.forall_mem_cons.2 ⟨subd9_2_961, List.forall_mem_cons.2 ⟨subd9_2_962, List.forall_mem_cons.2 ⟨subd9_2_963, List.forall_mem_cons.2 ⟨subd9_2_964, List.forall_mem_cons.2 ⟨subd9_2_965, List.forall_mem_cons.2 ⟨subd9_2_966, List.forall_mem_cons.2 ⟨subd9_2_967, List.forall_mem_cons.2 ⟨subd9_2_968, List.forall_mem_cons.2 ⟨subd9_2_969, List.forall_mem_cons.2 ⟨subd9_2_970, List.forall_mem_cons.2 ⟨subd9_2_971, List.forall_mem_cons.2 ⟨subd9_2_972, List.forall_mem_cons.2 ⟨subd9_2_973, List.forall_mem_cons.2 ⟨subd9_2_974, List.forall_mem_cons.2 ⟨subd9_2_975, List.forall_mem_cons.2 ⟨subd9_2_976, List.forall_mem_cons.2 ⟨subd9_2_977, List.forall_mem_cons.2 ⟨subd9_2_978, List.forall_mem_cons.2 ⟨subd9_2_979, List.forall_mem_cons.2 ⟨subd9_2_980, List.forall_mem_cons.2 ⟨subd9_2_981, List.forall_mem_cons.2 ⟨subd9_2_982, List.forall_mem_cons.2 ⟨subd9_2_983, List.forall_mem_cons.2 ⟨subd9_2_984, List.forall_mem_cons.2 ⟨subd9_2_985, List.forall_mem_cons.2 ⟨subd9_2_986, List.forall_mem_cons.2 ⟨subd9_2_987, List.forall_mem_cons.2 ⟨subd9_2_988, List.forall_mem_cons.2 ⟨subd9_2_989, List.forall_mem_cons.2 ⟨subd9_2_990, List.forall_mem_cons.2 ⟨subd9_2_991, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_2_992 : subd9_2 [4, -2, 1] = true := by decide +kernel
theorem subd9_2_993 : subd9_2 [4, -2, 2] = true := by decide +kernel
theorem subd9_2_994 : subd9_2 [4, -2, 3] = true := by decide +kernel
theorem subd9_2_995 : subd9_2 [4, -2, 4] = true := by decide +kernel
theorem subd9_2_996 : subd9_2 [4, -2, 5] = true := by decide +kernel
theorem subd9_2_997 : subd9_2 [4, -2, 6] = true := by decide +kernel
theorem subd9_2_998 : subd9_2 [4, -2, 7] = true := by decide +kernel
theorem subd9_2_999 : subd9_2 [4, -1, -6] = true := by decide +kernel
theorem subd9_2_1000 : subd9_2 [4, -1, -5] = true := by decide +kernel
theorem subd9_2_1001 : subd9_2 [4, -1, -4] = true := by decide +kernel
theorem subd9_2_1002 : subd9_2 [4, -1, -3] = true := by decide +kernel
theorem subd9_2_1003 : subd9_2 [4, -1, -2] = true := by decide +kernel
theorem subd9_2_1004 : subd9_2 [4, -1, -1] = true := by decide +kernel
theorem subd9_2_1005 : subd9_2 [4, -1, 0] = true := by decide +kernel
theorem subd9_2_1006 : subd9_2 [4, -1, 1] = true := by decide +kernel
theorem subd9_2_1007 : subd9_2 [4, -1, 2] = true := by decide +kernel
theorem subd9_2_1008 : subd9_2 [4, -1, 3] = true := by decide +kernel
theorem subd9_2_1009 : subd9_2 [4, -1, 4] = true := by decide +kernel
theorem subd9_2_1010 : subd9_2 [4, -1, 5] = true := by decide +kernel
theorem subd9_2_1011 : subd9_2 [4, -1, 6] = true := by decide +kernel
theorem subd9_2_1012 : subd9_2 [4, -1, 7] = true := by decide +kernel
theorem subd9_2_1013 : subd9_2 [4, 0, -6] = true := by decide +kernel
theorem subd9_2_1014 : subd9_2 [4, 0, -5] = true := by decide +kernel
theorem subd9_2_1015 : subd9_2 [4, 0, -4] = true := by decide +kernel
theorem subd9_2_1016 : subd9_2 [4, 0, -3] = true := by decide +kernel
theorem subd9_2_1017 : subd9_2 [4, 0, -2] = true := by decide +kernel
theorem subd9_2_1018 : subd9_2 [4, 0, -1] = true := by decide +kernel
theorem subd9_2_1019 : subd9_2 [4, 0, 0] = true := by decide +kernel
theorem subd9_2_1020 : subd9_2 [4, 0, 1] = true := by decide +kernel
theorem subd9_2_1021 : subd9_2 [4, 0, 2] = true := by decide +kernel
theorem subd9_2_1022 : subd9_2 [4, 0, 3] = true := by decide +kernel
theorem subd9_2_1023 : subd9_2 [4, 0, 4] = true := by decide +kernel
theorem sbd9_2_31 : ∀ q ∈ blkd9_2_31, subd9_2 q = true := by
  unfold blkd9_2_31
  exact List.forall_mem_cons.2 ⟨subd9_2_992, List.forall_mem_cons.2 ⟨subd9_2_993, List.forall_mem_cons.2 ⟨subd9_2_994, List.forall_mem_cons.2 ⟨subd9_2_995, List.forall_mem_cons.2 ⟨subd9_2_996, List.forall_mem_cons.2 ⟨subd9_2_997, List.forall_mem_cons.2 ⟨subd9_2_998, List.forall_mem_cons.2 ⟨subd9_2_999, List.forall_mem_cons.2 ⟨subd9_2_1000, List.forall_mem_cons.2 ⟨subd9_2_1001, List.forall_mem_cons.2 ⟨subd9_2_1002, List.forall_mem_cons.2 ⟨subd9_2_1003, List.forall_mem_cons.2 ⟨subd9_2_1004, List.forall_mem_cons.2 ⟨subd9_2_1005, List.forall_mem_cons.2 ⟨subd9_2_1006, List.forall_mem_cons.2 ⟨subd9_2_1007, List.forall_mem_cons.2 ⟨subd9_2_1008, List.forall_mem_cons.2 ⟨subd9_2_1009, List.forall_mem_cons.2 ⟨subd9_2_1010, List.forall_mem_cons.2 ⟨subd9_2_1011, List.forall_mem_cons.2 ⟨subd9_2_1012, List.forall_mem_cons.2 ⟨subd9_2_1013, List.forall_mem_cons.2 ⟨subd9_2_1014, List.forall_mem_cons.2 ⟨subd9_2_1015, List.forall_mem_cons.2 ⟨subd9_2_1016, List.forall_mem_cons.2 ⟨subd9_2_1017, List.forall_mem_cons.2 ⟨subd9_2_1018, List.forall_mem_cons.2 ⟨subd9_2_1019, List.forall_mem_cons.2 ⟨subd9_2_1020, List.forall_mem_cons.2 ⟨subd9_2_1021, List.forall_mem_cons.2 ⟨subd9_2_1022, List.forall_mem_cons.2 ⟨subd9_2_1023, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_2_1024 : subd9_2 [4, 0, 5] = true := by decide +kernel
theorem subd9_2_1025 : subd9_2 [4, 0, 6] = true := by decide +kernel
theorem subd9_2_1026 : subd9_2 [4, 0, 7] = true := by decide +kernel
theorem subd9_2_1027 : subd9_2 [4, 1] = true := by decide +kernel
theorem subd9_2_1028 : subd9_2 [4, 2] = true := by decide +kernel
theorem subd9_2_1029 : subd9_2 [4, 3] = true := by decide +kernel
theorem subd9_2_1030 : subd9_2 [4, 4] = true := by decide +kernel
theorem subd9_2_1031 : subd9_2 [4, 5] = true := by decide +kernel
theorem subd9_2_1032 : subd9_2 [4, 6] = true := by decide +kernel
theorem subd9_2_1033 : subd9_2 [5, -8] = true := by decide +kernel
theorem subd9_2_1034 : subd9_2 [5, -7] = true := by decide +kernel
theorem subd9_2_1035 : subd9_2 [5, -6] = true := by decide +kernel
theorem subd9_2_1036 : subd9_2 [5, -5] = true := by decide +kernel
theorem subd9_2_1037 : subd9_2 [5, -4] = true := by decide +kernel
theorem subd9_2_1038 : subd9_2 [5, -3] = true := by decide +kernel
theorem subd9_2_1039 : subd9_2 [5, -2] = true := by decide +kernel
theorem subd9_2_1040 : subd9_2 [5, -1] = true := by decide +kernel
theorem subd9_2_1041 : subd9_2 [5, 0] = true := by decide +kernel
theorem subd9_2_1042 : subd9_2 [5, 1] = true := by decide +kernel
theorem subd9_2_1043 : subd9_2 [5, 2] = true := by decide +kernel
theorem subd9_2_1044 : subd9_2 [5, 3] = true := by decide +kernel
theorem subd9_2_1045 : subd9_2 [5, 4] = true := by decide +kernel
theorem subd9_2_1046 : subd9_2 [5, 5] = true := by decide +kernel
theorem subd9_2_1047 : subd9_2 [6, -8] = true := by decide +kernel
theorem subd9_2_1048 : subd9_2 [6, -7] = true := by decide +kernel
theorem subd9_2_1049 : subd9_2 [6, -6] = true := by decide +kernel
theorem subd9_2_1050 : subd9_2 [6, -5] = true := by decide +kernel
theorem subd9_2_1051 : subd9_2 [6, -4] = true := by decide +kernel
theorem subd9_2_1052 : subd9_2 [6, -3] = true := by decide +kernel
theorem subd9_2_1053 : subd9_2 [6, -2] = true := by decide +kernel
theorem subd9_2_1054 : subd9_2 [6, -1] = true := by decide +kernel
theorem subd9_2_1055 : subd9_2 [6, 0] = true := by decide +kernel
theorem sbd9_2_32 : ∀ q ∈ blkd9_2_32, subd9_2 q = true := by
  unfold blkd9_2_32
  exact List.forall_mem_cons.2 ⟨subd9_2_1024, List.forall_mem_cons.2 ⟨subd9_2_1025, List.forall_mem_cons.2 ⟨subd9_2_1026, List.forall_mem_cons.2 ⟨subd9_2_1027, List.forall_mem_cons.2 ⟨subd9_2_1028, List.forall_mem_cons.2 ⟨subd9_2_1029, List.forall_mem_cons.2 ⟨subd9_2_1030, List.forall_mem_cons.2 ⟨subd9_2_1031, List.forall_mem_cons.2 ⟨subd9_2_1032, List.forall_mem_cons.2 ⟨subd9_2_1033, List.forall_mem_cons.2 ⟨subd9_2_1034, List.forall_mem_cons.2 ⟨subd9_2_1035, List.forall_mem_cons.2 ⟨subd9_2_1036, List.forall_mem_cons.2 ⟨subd9_2_1037, List.forall_mem_cons.2 ⟨subd9_2_1038, List.forall_mem_cons.2 ⟨subd9_2_1039, List.forall_mem_cons.2 ⟨subd9_2_1040, List.forall_mem_cons.2 ⟨subd9_2_1041, List.forall_mem_cons.2 ⟨subd9_2_1042, List.forall_mem_cons.2 ⟨subd9_2_1043, List.forall_mem_cons.2 ⟨subd9_2_1044, List.forall_mem_cons.2 ⟨subd9_2_1045, List.forall_mem_cons.2 ⟨subd9_2_1046, List.forall_mem_cons.2 ⟨subd9_2_1047, List.forall_mem_cons.2 ⟨subd9_2_1048, List.forall_mem_cons.2 ⟨subd9_2_1049, List.forall_mem_cons.2 ⟨subd9_2_1050, List.forall_mem_cons.2 ⟨subd9_2_1051, List.forall_mem_cons.2 ⟨subd9_2_1052, List.forall_mem_cons.2 ⟨subd9_2_1053, List.forall_mem_cons.2 ⟨subd9_2_1054, List.forall_mem_cons.2 ⟨subd9_2_1055, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_2_1056 : subd9_2 [6, 1] = true := by decide +kernel
theorem subd9_2_1057 : subd9_2 [6, 2] = true := by decide +kernel
theorem subd9_2_1058 : subd9_2 [6, 3] = true := by decide +kernel
theorem subd9_2_1059 : subd9_2 [6, 4] = true := by decide +kernel
theorem subd9_2_1060 : subd9_2 [7, -6] = true := by decide +kernel
theorem subd9_2_1061 : subd9_2 [7, -5] = true := by decide +kernel
theorem subd9_2_1062 : subd9_2 [7, -4] = true := by decide +kernel
theorem subd9_2_1063 : subd9_2 [7, -3] = true := by decide +kernel
theorem subd9_2_1064 : subd9_2 [7, -2] = true := by decide +kernel
theorem subd9_2_1065 : subd9_2 [7, -1] = true := by decide +kernel
theorem subd9_2_1066 : subd9_2 [7, 0] = true := by decide +kernel
theorem subd9_2_1067 : subd9_2 [7, 1] = true := by decide +kernel
theorem subd9_2_1068 : subd9_2 [7, 2] = true := by decide +kernel
theorem subd9_2_1069 : subd9_2 [7, 3] = true := by decide +kernel
theorem subd9_2_1070 : subd9_2 [8] = true := by decide +kernel
theorem sbd9_2_33 : ∀ q ∈ blkd9_2_33, subd9_2 q = true := by
  unfold blkd9_2_33
  exact List.forall_mem_cons.2 ⟨subd9_2_1056, List.forall_mem_cons.2 ⟨subd9_2_1057, List.forall_mem_cons.2 ⟨subd9_2_1058, List.forall_mem_cons.2 ⟨subd9_2_1059, List.forall_mem_cons.2 ⟨subd9_2_1060, List.forall_mem_cons.2 ⟨subd9_2_1061, List.forall_mem_cons.2 ⟨subd9_2_1062, List.forall_mem_cons.2 ⟨subd9_2_1063, List.forall_mem_cons.2 ⟨subd9_2_1064, List.forall_mem_cons.2 ⟨subd9_2_1065, List.forall_mem_cons.2 ⟨subd9_2_1066, List.forall_mem_cons.2 ⟨subd9_2_1067, List.forall_mem_cons.2 ⟨subd9_2_1068, List.forall_mem_cons.2 ⟨subd9_2_1069, List.forall_mem_cons.2 ⟨subd9_2_1070, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd9_3 : ldCheck G d9_3.U d9_3.ms ldd9_3 = true := by decide +kernel
theorem pre_okd9_3 : subPre G cell9 d9_3 = true := by decide +kernel
theorem subd9_3_0 : subd9_3 [-3] = true := by decide +kernel
theorem subd9_3_1 : subd9_3 [-2, -3] = true := by decide +kernel
theorem subd9_3_2 : subd9_3 [-2, -2] = true := by decide +kernel
theorem subd9_3_3 : subd9_3 [-2, -1] = true := by decide +kernel
theorem subd9_3_4 : subd9_3 [-2, 0] = true := by decide +kernel
theorem subd9_3_5 : subd9_3 [-2, 1] = true := by decide +kernel
theorem subd9_3_6 : subd9_3 [-2, 2] = true := by decide +kernel
theorem subd9_3_7 : subd9_3 [-1, -4] = true := by decide +kernel
theorem subd9_3_8 : subd9_3 [-1, -3] = true := by decide +kernel
theorem subd9_3_9 : subd9_3 [-1, -2] = true := by decide +kernel
theorem subd9_3_10 : subd9_3 [-1, -1] = true := by decide +kernel
theorem subd9_3_11 : subd9_3 [-1, 0] = true := by decide +kernel
theorem subd9_3_12 : subd9_3 [-1, 1] = true := by decide +kernel
theorem subd9_3_13 : subd9_3 [-1, 2] = true := by decide +kernel
theorem subd9_3_14 : subd9_3 [-1, 3] = true := by decide +kernel
theorem subd9_3_15 : subd9_3 [0, -4] = true := by decide +kernel
theorem subd9_3_16 : subd9_3 [0, -3] = true := by decide +kernel
theorem subd9_3_17 : subd9_3 [0, -2] = true := by decide +kernel
theorem subd9_3_18 : subd9_3 [0, -1] = true := by decide +kernel
theorem subd9_3_19 : subd9_3 [0, 0] = true := by decide +kernel
theorem subd9_3_20 : subd9_3 [0, 1] = true := by decide +kernel
theorem subd9_3_21 : subd9_3 [0, 2] = true := by decide +kernel
theorem subd9_3_22 : subd9_3 [0, 3] = true := by decide +kernel
theorem subd9_3_23 : subd9_3 [1, -4] = true := by decide +kernel
theorem subd9_3_24 : subd9_3 [1, -3] = true := by decide +kernel
theorem subd9_3_25 : subd9_3 [1, -2] = true := by decide +kernel
theorem subd9_3_26 : subd9_3 [1, -1] = true := by decide +kernel
theorem subd9_3_27 : subd9_3 [1, 0] = true := by decide +kernel
theorem subd9_3_28 : subd9_3 [1, 1] = true := by decide +kernel
theorem subd9_3_29 : subd9_3 [1, 2] = true := by decide +kernel
theorem subd9_3_30 : subd9_3 [1, 3] = true := by decide +kernel
theorem subd9_3_31 : subd9_3 [2, -3] = true := by decide +kernel
theorem sbd9_3_0 : ∀ q ∈ blkd9_3_0, subd9_3 q = true := by
  unfold blkd9_3_0
  exact List.forall_mem_cons.2 ⟨subd9_3_0, List.forall_mem_cons.2 ⟨subd9_3_1, List.forall_mem_cons.2 ⟨subd9_3_2, List.forall_mem_cons.2 ⟨subd9_3_3, List.forall_mem_cons.2 ⟨subd9_3_4, List.forall_mem_cons.2 ⟨subd9_3_5, List.forall_mem_cons.2 ⟨subd9_3_6, List.forall_mem_cons.2 ⟨subd9_3_7, List.forall_mem_cons.2 ⟨subd9_3_8, List.forall_mem_cons.2 ⟨subd9_3_9, List.forall_mem_cons.2 ⟨subd9_3_10, List.forall_mem_cons.2 ⟨subd9_3_11, List.forall_mem_cons.2 ⟨subd9_3_12, List.forall_mem_cons.2 ⟨subd9_3_13, List.forall_mem_cons.2 ⟨subd9_3_14, List.forall_mem_cons.2 ⟨subd9_3_15, List.forall_mem_cons.2 ⟨subd9_3_16, List.forall_mem_cons.2 ⟨subd9_3_17, List.forall_mem_cons.2 ⟨subd9_3_18, List.forall_mem_cons.2 ⟨subd9_3_19, List.forall_mem_cons.2 ⟨subd9_3_20, List.forall_mem_cons.2 ⟨subd9_3_21, List.forall_mem_cons.2 ⟨subd9_3_22, List.forall_mem_cons.2 ⟨subd9_3_23, List.forall_mem_cons.2 ⟨subd9_3_24, List.forall_mem_cons.2 ⟨subd9_3_25, List.forall_mem_cons.2 ⟨subd9_3_26, List.forall_mem_cons.2 ⟨subd9_3_27, List.forall_mem_cons.2 ⟨subd9_3_28, List.forall_mem_cons.2 ⟨subd9_3_29, List.forall_mem_cons.2 ⟨subd9_3_30, List.forall_mem_cons.2 ⟨subd9_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C121
