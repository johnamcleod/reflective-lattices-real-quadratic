import ReflectZphi.Data.Cert5.C074.Base

namespace ReflectZphi.Data.Cert5.C074
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub11_928 : sub11 [3, 0, -9] = true := by decide +kernel
theorem sub11_929 : sub11 [3, 0, -8] = true := by decide +kernel
theorem sub11_930 : sub11 [3, 0, -7] = true := by decide +kernel
theorem sub11_931 : sub11 [3, 0, -6] = true := by decide +kernel
theorem sub11_932 : sub11 [3, 0, -5] = true := by decide +kernel
theorem sub11_933 : sub11 [3, 0, -4] = true := by decide +kernel
theorem sub11_934 : sub11 [3, 0, -3] = true := by decide +kernel
theorem sub11_935 : sub11 [3, 0, -2] = true := by decide +kernel
theorem sub11_936 : sub11 [3, 0, -1] = true := by decide +kernel
theorem sub11_937 : sub11 [3, 0, 0] = true := by decide +kernel
theorem sub11_938 : sub11 [3, 0, 1] = true := by decide +kernel
theorem sub11_939 : sub11 [3, 0, 2] = true := by decide +kernel
theorem sub11_940 : sub11 [3, 0, 3] = true := by decide +kernel
theorem sub11_941 : sub11 [3, 0, 4] = true := by decide +kernel
theorem sub11_942 : sub11 [3, 0, 5] = true := by decide +kernel
theorem sub11_943 : sub11 [3, 0, 6] = true := by decide +kernel
theorem sub11_944 : sub11 [3, 0, 7] = true := by decide +kernel
theorem sub11_945 : sub11 [3, 1, -8] = true := by decide +kernel
theorem sub11_946 : sub11 [3, 1, -7] = true := by decide +kernel
theorem sub11_947 : sub11 [3, 1, -6] = true := by decide +kernel
theorem sub11_948 : sub11 [3, 1, -5] = true := by decide +kernel
theorem sub11_949 : sub11 [3, 1, -4] = true := by decide +kernel
theorem sub11_950 : sub11 [3, 1, -3] = true := by decide +kernel
theorem sub11_951 : sub11 [3, 1, -2] = true := by decide +kernel
theorem sub11_952 : sub11 [3, 1, -1] = true := by decide +kernel
theorem sub11_953 : sub11 [3, 1, 0] = true := by decide +kernel
theorem sub11_954 : sub11 [3, 1, 1] = true := by decide +kernel
theorem sub11_955 : sub11 [3, 1, 2] = true := by decide +kernel
theorem sub11_956 : sub11 [3, 1, 3] = true := by decide +kernel
theorem sub11_957 : sub11 [3, 1, 4] = true := by decide +kernel
theorem sub11_958 : sub11 [3, 1, 5] = true := by decide +kernel
theorem sub11_959 : sub11 [3, 1, 6] = true := by decide +kernel
theorem sb11_29 : ∀ q ∈ blk11_29, sub11 q = true := by
  unfold blk11_29
  exact List.forall_mem_cons.2 ⟨sub11_928, List.forall_mem_cons.2 ⟨sub11_929, List.forall_mem_cons.2 ⟨sub11_930, List.forall_mem_cons.2 ⟨sub11_931, List.forall_mem_cons.2 ⟨sub11_932, List.forall_mem_cons.2 ⟨sub11_933, List.forall_mem_cons.2 ⟨sub11_934, List.forall_mem_cons.2 ⟨sub11_935, List.forall_mem_cons.2 ⟨sub11_936, List.forall_mem_cons.2 ⟨sub11_937, List.forall_mem_cons.2 ⟨sub11_938, List.forall_mem_cons.2 ⟨sub11_939, List.forall_mem_cons.2 ⟨sub11_940, List.forall_mem_cons.2 ⟨sub11_941, List.forall_mem_cons.2 ⟨sub11_942, List.forall_mem_cons.2 ⟨sub11_943, List.forall_mem_cons.2 ⟨sub11_944, List.forall_mem_cons.2 ⟨sub11_945, List.forall_mem_cons.2 ⟨sub11_946, List.forall_mem_cons.2 ⟨sub11_947, List.forall_mem_cons.2 ⟨sub11_948, List.forall_mem_cons.2 ⟨sub11_949, List.forall_mem_cons.2 ⟨sub11_950, List.forall_mem_cons.2 ⟨sub11_951, List.forall_mem_cons.2 ⟨sub11_952, List.forall_mem_cons.2 ⟨sub11_953, List.forall_mem_cons.2 ⟨sub11_954, List.forall_mem_cons.2 ⟨sub11_955, List.forall_mem_cons.2 ⟨sub11_956, List.forall_mem_cons.2 ⟨sub11_957, List.forall_mem_cons.2 ⟨sub11_958, List.forall_mem_cons.2 ⟨sub11_959, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub11_960 : sub11 [3, 1, 7] = true := by decide +kernel
theorem sub11_961 : sub11 [3, 2, -8] = true := by decide +kernel
theorem sub11_962 : sub11 [3, 2, -7] = true := by decide +kernel
theorem sub11_963 : sub11 [3, 2, -6] = true := by decide +kernel
theorem sub11_964 : sub11 [3, 2, -5] = true := by decide +kernel
theorem sub11_965 : sub11 [3, 2, -4] = true := by decide +kernel
theorem sub11_966 : sub11 [3, 2, -3] = true := by decide +kernel
theorem sub11_967 : sub11 [3, 2, -2] = true := by decide +kernel
theorem sub11_968 : sub11 [3, 2, -1] = true := by decide +kernel
theorem sub11_969 : sub11 [3, 2, 0] = true := by decide +kernel
theorem sub11_970 : sub11 [3, 2, 1] = true := by decide +kernel
theorem sub11_971 : sub11 [3, 2, 2] = true := by decide +kernel
theorem sub11_972 : sub11 [3, 2, 3] = true := by decide +kernel
theorem sub11_973 : sub11 [3, 2, 4] = true := by decide +kernel
theorem sub11_974 : sub11 [3, 2, 5] = true := by decide +kernel
theorem sub11_975 : sub11 [3, 2, 6] = true := by decide +kernel
theorem sub11_976 : sub11 [3, 2, 7] = true := by decide +kernel
theorem sub11_977 : sub11 [3, 3, -6] = true := by decide +kernel
theorem sub11_978 : sub11 [3, 3, -5] = true := by decide +kernel
theorem sub11_979 : sub11 [3, 3, -4] = true := by decide +kernel
theorem sub11_980 : sub11 [3, 3, -3] = true := by decide +kernel
theorem sub11_981 : sub11 [3, 3, -2] = true := by decide +kernel
theorem sub11_982 : sub11 [3, 3, -1] = true := by decide +kernel
theorem sub11_983 : sub11 [3, 3, 0] = true := by decide +kernel
theorem sub11_984 : sub11 [3, 3, 1] = true := by decide +kernel
theorem sub11_985 : sub11 [3, 3, 2] = true := by decide +kernel
theorem sub11_986 : sub11 [3, 3, 3] = true := by decide +kernel
theorem sub11_987 : sub11 [3, 3, 4] = true := by decide +kernel
theorem sub11_988 : sub11 [3, 3, 5] = true := by decide +kernel
theorem sub11_989 : sub11 [3, 3, 6] = true := by decide +kernel
theorem sub11_990 : sub11 [3, 3, 7] = true := by decide +kernel
theorem sub11_991 : sub11 [3, 4] = true := by decide +kernel
theorem sb11_30 : ∀ q ∈ blk11_30, sub11 q = true := by
  unfold blk11_30
  exact List.forall_mem_cons.2 ⟨sub11_960, List.forall_mem_cons.2 ⟨sub11_961, List.forall_mem_cons.2 ⟨sub11_962, List.forall_mem_cons.2 ⟨sub11_963, List.forall_mem_cons.2 ⟨sub11_964, List.forall_mem_cons.2 ⟨sub11_965, List.forall_mem_cons.2 ⟨sub11_966, List.forall_mem_cons.2 ⟨sub11_967, List.forall_mem_cons.2 ⟨sub11_968, List.forall_mem_cons.2 ⟨sub11_969, List.forall_mem_cons.2 ⟨sub11_970, List.forall_mem_cons.2 ⟨sub11_971, List.forall_mem_cons.2 ⟨sub11_972, List.forall_mem_cons.2 ⟨sub11_973, List.forall_mem_cons.2 ⟨sub11_974, List.forall_mem_cons.2 ⟨sub11_975, List.forall_mem_cons.2 ⟨sub11_976, List.forall_mem_cons.2 ⟨sub11_977, List.forall_mem_cons.2 ⟨sub11_978, List.forall_mem_cons.2 ⟨sub11_979, List.forall_mem_cons.2 ⟨sub11_980, List.forall_mem_cons.2 ⟨sub11_981, List.forall_mem_cons.2 ⟨sub11_982, List.forall_mem_cons.2 ⟨sub11_983, List.forall_mem_cons.2 ⟨sub11_984, List.forall_mem_cons.2 ⟨sub11_985, List.forall_mem_cons.2 ⟨sub11_986, List.forall_mem_cons.2 ⟨sub11_987, List.forall_mem_cons.2 ⟨sub11_988, List.forall_mem_cons.2 ⟨sub11_989, List.forall_mem_cons.2 ⟨sub11_990, List.forall_mem_cons.2 ⟨sub11_991, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub11_992 : sub11 [3, 5] = true := by decide +kernel
theorem sub11_993 : sub11 [4, -4] = true := by decide +kernel
theorem sub11_994 : sub11 [4, -3] = true := by decide +kernel
theorem sub11_995 : sub11 [4, -2] = true := by decide +kernel
theorem sub11_996 : sub11 [4, -1] = true := by decide +kernel
theorem sub11_997 : sub11 [4, 0, -8] = true := by decide +kernel
theorem sub11_998 : sub11 [4, 0, -7] = true := by decide +kernel
theorem sub11_999 : sub11 [4, 0, -6] = true := by decide +kernel
theorem sub11_1000 : sub11 [4, 0, -5] = true := by decide +kernel
theorem sub11_1001 : sub11 [4, 0, -4] = true := by decide +kernel
theorem sub11_1002 : sub11 [4, 0, -3] = true := by decide +kernel
theorem sub11_1003 : sub11 [4, 0, -2] = true := by decide +kernel
theorem sub11_1004 : sub11 [4, 0, -1] = true := by decide +kernel
theorem sub11_1005 : sub11 [4, 0, 0] = true := by decide +kernel
theorem sub11_1006 : sub11 [4, 0, 1] = true := by decide +kernel
theorem sub11_1007 : sub11 [4, 0, 2] = true := by decide +kernel
theorem sub11_1008 : sub11 [4, 0, 3] = true := by decide +kernel
theorem sub11_1009 : sub11 [4, 0, 4] = true := by decide +kernel
theorem sub11_1010 : sub11 [4, 0, 5] = true := by decide +kernel
theorem sub11_1011 : sub11 [4, 1, -7] = true := by decide +kernel
theorem sub11_1012 : sub11 [4, 1, -6] = true := by decide +kernel
theorem sub11_1013 : sub11 [4, 1, -5] = true := by decide +kernel
theorem sub11_1014 : sub11 [4, 1, -4] = true := by decide +kernel
theorem sub11_1015 : sub11 [4, 1, -3] = true := by decide +kernel
theorem sub11_1016 : sub11 [4, 1, -2] = true := by decide +kernel
theorem sub11_1017 : sub11 [4, 1, -1] = true := by decide +kernel
theorem sub11_1018 : sub11 [4, 1, 0] = true := by decide +kernel
theorem sub11_1019 : sub11 [4, 1, 1] = true := by decide +kernel
theorem sub11_1020 : sub11 [4, 1, 2] = true := by decide +kernel
theorem sub11_1021 : sub11 [4, 1, 3] = true := by decide +kernel
theorem sub11_1022 : sub11 [4, 1, 4] = true := by decide +kernel
theorem sub11_1023 : sub11 [4, 1, 5] = true := by decide +kernel
theorem sb11_31 : ∀ q ∈ blk11_31, sub11 q = true := by
  unfold blk11_31
  exact List.forall_mem_cons.2 ⟨sub11_992, List.forall_mem_cons.2 ⟨sub11_993, List.forall_mem_cons.2 ⟨sub11_994, List.forall_mem_cons.2 ⟨sub11_995, List.forall_mem_cons.2 ⟨sub11_996, List.forall_mem_cons.2 ⟨sub11_997, List.forall_mem_cons.2 ⟨sub11_998, List.forall_mem_cons.2 ⟨sub11_999, List.forall_mem_cons.2 ⟨sub11_1000, List.forall_mem_cons.2 ⟨sub11_1001, List.forall_mem_cons.2 ⟨sub11_1002, List.forall_mem_cons.2 ⟨sub11_1003, List.forall_mem_cons.2 ⟨sub11_1004, List.forall_mem_cons.2 ⟨sub11_1005, List.forall_mem_cons.2 ⟨sub11_1006, List.forall_mem_cons.2 ⟨sub11_1007, List.forall_mem_cons.2 ⟨sub11_1008, List.forall_mem_cons.2 ⟨sub11_1009, List.forall_mem_cons.2 ⟨sub11_1010, List.forall_mem_cons.2 ⟨sub11_1011, List.forall_mem_cons.2 ⟨sub11_1012, List.forall_mem_cons.2 ⟨sub11_1013, List.forall_mem_cons.2 ⟨sub11_1014, List.forall_mem_cons.2 ⟨sub11_1015, List.forall_mem_cons.2 ⟨sub11_1016, List.forall_mem_cons.2 ⟨sub11_1017, List.forall_mem_cons.2 ⟨sub11_1018, List.forall_mem_cons.2 ⟨sub11_1019, List.forall_mem_cons.2 ⟨sub11_1020, List.forall_mem_cons.2 ⟨sub11_1021, List.forall_mem_cons.2 ⟨sub11_1022, List.forall_mem_cons.2 ⟨sub11_1023, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub11_1024 : sub11 [4, 1, 6] = true := by decide +kernel
theorem sub11_1025 : sub11 [4, 2] = true := by decide +kernel
theorem sub11_1026 : sub11 [4, 3] = true := by decide +kernel
theorem sub11_1027 : sub11 [4, 4] = true := by decide +kernel
theorem sub11_1028 : sub11 [5, -3] = true := by decide +kernel
theorem sub11_1029 : sub11 [5, -2] = true := by decide +kernel
theorem sub11_1030 : sub11 [5, -1] = true := by decide +kernel
theorem sub11_1031 : sub11 [5, 0] = true := by decide +kernel
theorem sub11_1032 : sub11 [5, 1] = true := by decide +kernel
theorem sub11_1033 : sub11 [5, 2] = true := by decide +kernel
theorem sub11_1034 : sub11 [5, 3] = true := by decide +kernel
theorem sb11_32 : ∀ q ∈ blk11_32, sub11 q = true := by
  unfold blk11_32
  exact List.forall_mem_cons.2 ⟨sub11_1024, List.forall_mem_cons.2 ⟨sub11_1025, List.forall_mem_cons.2 ⟨sub11_1026, List.forall_mem_cons.2 ⟨sub11_1027, List.forall_mem_cons.2 ⟨sub11_1028, List.forall_mem_cons.2 ⟨sub11_1029, List.forall_mem_cons.2 ⟨sub11_1030, List.forall_mem_cons.2 ⟨sub11_1031, List.forall_mem_cons.2 ⟨sub11_1032, List.forall_mem_cons.2 ⟨sub11_1033, List.forall_mem_cons.2 ⟨sub11_1034, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C074
