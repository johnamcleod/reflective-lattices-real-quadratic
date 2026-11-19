import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd17_1_896 : subd17_1 [2, -5, 4] = true := by decide +kernel
theorem subd17_1_897 : subd17_1 [2, -5, 5] = true := by decide +kernel
theorem subd17_1_898 : subd17_1 [2, -5, 6] = true := by decide +kernel
theorem subd17_1_899 : subd17_1 [2, -4, -7] = true := by decide +kernel
theorem subd17_1_900 : subd17_1 [2, -4, -6] = true := by decide +kernel
theorem subd17_1_901 : subd17_1 [2, -4, -5] = true := by decide +kernel
theorem subd17_1_902 : subd17_1 [2, -4, -4] = true := by decide +kernel
theorem subd17_1_903 : subd17_1 [2, -4, -3] = true := by decide +kernel
theorem subd17_1_904 : subd17_1 [2, -4, -2] = true := by decide +kernel
theorem subd17_1_905 : subd17_1 [2, -4, -1] = true := by decide +kernel
theorem subd17_1_906 : subd17_1 [2, -4, 0] = true := by decide +kernel
theorem subd17_1_907 : subd17_1 [2, -4, 1] = true := by decide +kernel
theorem subd17_1_908 : subd17_1 [2, -4, 2] = true := by decide +kernel
theorem subd17_1_909 : subd17_1 [2, -4, 3] = true := by decide +kernel
theorem subd17_1_910 : subd17_1 [2, -4, 4] = true := by decide +kernel
theorem subd17_1_911 : subd17_1 [2, -4, 5] = true := by decide +kernel
theorem subd17_1_912 : subd17_1 [2, -4, 6] = true := by decide +kernel
theorem subd17_1_913 : subd17_1 [2, -4, 7] = true := by decide +kernel
theorem subd17_1_914 : subd17_1 [2, -3, -8] = true := by decide +kernel
theorem subd17_1_915 : subd17_1 [2, -3, -7] = true := by decide +kernel
theorem subd17_1_916 : subd17_1 [2, -3, -6] = true := by decide +kernel
theorem subd17_1_917 : subd17_1 [2, -3, -5] = true := by decide +kernel
theorem subd17_1_918 : subd17_1 [2, -3, -4] = true := by decide +kernel
theorem subd17_1_919 : subd17_1 [2, -3, -3] = true := by decide +kernel
theorem subd17_1_920 : subd17_1 [2, -3, -2] = true := by decide +kernel
theorem subd17_1_921 : subd17_1 [2, -3, -1] = true := by decide +kernel
theorem subd17_1_922 : subd17_1 [2, -3, 0] = true := by decide +kernel
theorem subd17_1_923 : subd17_1 [2, -3, 1] = true := by decide +kernel
theorem subd17_1_924 : subd17_1 [2, -3, 2] = true := by decide +kernel
theorem subd17_1_925 : subd17_1 [2, -3, 3] = true := by decide +kernel
theorem subd17_1_926 : subd17_1 [2, -3, 4] = true := by decide +kernel
theorem subd17_1_927 : subd17_1 [2, -3, 5] = true := by decide +kernel
theorem sbd17_1_28 : ∀ q ∈ blkd17_1_28, subd17_1 q = true := by
  unfold blkd17_1_28
  exact List.forall_mem_cons.2 ⟨subd17_1_896, List.forall_mem_cons.2 ⟨subd17_1_897, List.forall_mem_cons.2 ⟨subd17_1_898, List.forall_mem_cons.2 ⟨subd17_1_899, List.forall_mem_cons.2 ⟨subd17_1_900, List.forall_mem_cons.2 ⟨subd17_1_901, List.forall_mem_cons.2 ⟨subd17_1_902, List.forall_mem_cons.2 ⟨subd17_1_903, List.forall_mem_cons.2 ⟨subd17_1_904, List.forall_mem_cons.2 ⟨subd17_1_905, List.forall_mem_cons.2 ⟨subd17_1_906, List.forall_mem_cons.2 ⟨subd17_1_907, List.forall_mem_cons.2 ⟨subd17_1_908, List.forall_mem_cons.2 ⟨subd17_1_909, List.forall_mem_cons.2 ⟨subd17_1_910, List.forall_mem_cons.2 ⟨subd17_1_911, List.forall_mem_cons.2 ⟨subd17_1_912, List.forall_mem_cons.2 ⟨subd17_1_913, List.forall_mem_cons.2 ⟨subd17_1_914, List.forall_mem_cons.2 ⟨subd17_1_915, List.forall_mem_cons.2 ⟨subd17_1_916, List.forall_mem_cons.2 ⟨subd17_1_917, List.forall_mem_cons.2 ⟨subd17_1_918, List.forall_mem_cons.2 ⟨subd17_1_919, List.forall_mem_cons.2 ⟨subd17_1_920, List.forall_mem_cons.2 ⟨subd17_1_921, List.forall_mem_cons.2 ⟨subd17_1_922, List.forall_mem_cons.2 ⟨subd17_1_923, List.forall_mem_cons.2 ⟨subd17_1_924, List.forall_mem_cons.2 ⟨subd17_1_925, List.forall_mem_cons.2 ⟨subd17_1_926, List.forall_mem_cons.2 ⟨subd17_1_927, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_1_928 : subd17_1 [2, -3, 6] = true := by decide +kernel
theorem subd17_1_929 : subd17_1 [2, -3, 7] = true := by decide +kernel
theorem subd17_1_930 : subd17_1 [2, -3, 8] = true := by decide +kernel
theorem subd17_1_931 : subd17_1 [2, -2, -8] = true := by decide +kernel
theorem subd17_1_932 : subd17_1 [2, -2, -7] = true := by decide +kernel
theorem subd17_1_933 : subd17_1 [2, -2, -6] = true := by decide +kernel
theorem subd17_1_934 : subd17_1 [2, -2, -5] = true := by decide +kernel
theorem subd17_1_935 : subd17_1 [2, -2, -4] = true := by decide +kernel
theorem subd17_1_936 : subd17_1 [2, -2, -3] = true := by decide +kernel
theorem subd17_1_937 : subd17_1 [2, -2, -2] = true := by decide +kernel
theorem subd17_1_938 : subd17_1 [2, -2, -1] = true := by decide +kernel
theorem subd17_1_939 : subd17_1 [2, -2, 0] = true := by decide +kernel
theorem subd17_1_940 : subd17_1 [2, -2, 1] = true := by decide +kernel
theorem subd17_1_941 : subd17_1 [2, -2, 2] = true := by decide +kernel
theorem subd17_1_942 : subd17_1 [2, -2, 3] = true := by decide +kernel
theorem subd17_1_943 : subd17_1 [2, -2, 4] = true := by decide +kernel
theorem subd17_1_944 : subd17_1 [2, -2, 5] = true := by decide +kernel
theorem subd17_1_945 : subd17_1 [2, -2, 6] = true := by decide +kernel
theorem subd17_1_946 : subd17_1 [2, -2, 7] = true := by decide +kernel
theorem subd17_1_947 : subd17_1 [2, -2, 8] = true := by decide +kernel
theorem subd17_1_948 : subd17_1 [2, -1, -8] = true := by decide +kernel
theorem subd17_1_949 : subd17_1 [2, -1, -7] = true := by decide +kernel
theorem subd17_1_950 : subd17_1 [2, -1, -6] = true := by decide +kernel
theorem subd17_1_951 : subd17_1 [2, -1, -5] = true := by decide +kernel
theorem subd17_1_952 : subd17_1 [2, -1, -4] = true := by decide +kernel
theorem subd17_1_953 : subd17_1 [2, -1, -3] = true := by decide +kernel
theorem subd17_1_954 : subd17_1 [2, -1, -2] = true := by decide +kernel
theorem subd17_1_955 : subd17_1 [2, -1, -1] = true := by decide +kernel
theorem subd17_1_956 : subd17_1 [2, -1, 0] = true := by decide +kernel
theorem subd17_1_957 : subd17_1 [2, -1, 1] = true := by decide +kernel
theorem subd17_1_958 : subd17_1 [2, -1, 2] = true := by decide +kernel
theorem subd17_1_959 : subd17_1 [2, -1, 3] = true := by decide +kernel
theorem sbd17_1_29 : ∀ q ∈ blkd17_1_29, subd17_1 q = true := by
  unfold blkd17_1_29
  exact List.forall_mem_cons.2 ⟨subd17_1_928, List.forall_mem_cons.2 ⟨subd17_1_929, List.forall_mem_cons.2 ⟨subd17_1_930, List.forall_mem_cons.2 ⟨subd17_1_931, List.forall_mem_cons.2 ⟨subd17_1_932, List.forall_mem_cons.2 ⟨subd17_1_933, List.forall_mem_cons.2 ⟨subd17_1_934, List.forall_mem_cons.2 ⟨subd17_1_935, List.forall_mem_cons.2 ⟨subd17_1_936, List.forall_mem_cons.2 ⟨subd17_1_937, List.forall_mem_cons.2 ⟨subd17_1_938, List.forall_mem_cons.2 ⟨subd17_1_939, List.forall_mem_cons.2 ⟨subd17_1_940, List.forall_mem_cons.2 ⟨subd17_1_941, List.forall_mem_cons.2 ⟨subd17_1_942, List.forall_mem_cons.2 ⟨subd17_1_943, List.forall_mem_cons.2 ⟨subd17_1_944, List.forall_mem_cons.2 ⟨subd17_1_945, List.forall_mem_cons.2 ⟨subd17_1_946, List.forall_mem_cons.2 ⟨subd17_1_947, List.forall_mem_cons.2 ⟨subd17_1_948, List.forall_mem_cons.2 ⟨subd17_1_949, List.forall_mem_cons.2 ⟨subd17_1_950, List.forall_mem_cons.2 ⟨subd17_1_951, List.forall_mem_cons.2 ⟨subd17_1_952, List.forall_mem_cons.2 ⟨subd17_1_953, List.forall_mem_cons.2 ⟨subd17_1_954, List.forall_mem_cons.2 ⟨subd17_1_955, List.forall_mem_cons.2 ⟨subd17_1_956, List.forall_mem_cons.2 ⟨subd17_1_957, List.forall_mem_cons.2 ⟨subd17_1_958, List.forall_mem_cons.2 ⟨subd17_1_959, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_1_960 : subd17_1 [2, -1, 4] = true := by decide +kernel
theorem subd17_1_961 : subd17_1 [2, -1, 5] = true := by decide +kernel
theorem subd17_1_962 : subd17_1 [2, -1, 6] = true := by decide +kernel
theorem subd17_1_963 : subd17_1 [2, -1, 7] = true := by decide +kernel
theorem subd17_1_964 : subd17_1 [2, -1, 8] = true := by decide +kernel
theorem subd17_1_965 : subd17_1 [2, -1, 9] = true := by decide +kernel
theorem subd17_1_966 : subd17_1 [2, 0, -8] = true := by decide +kernel
theorem subd17_1_967 : subd17_1 [2, 0, -7] = true := by decide +kernel
theorem subd17_1_968 : subd17_1 [2, 0, -6] = true := by decide +kernel
theorem subd17_1_969 : subd17_1 [2, 0, -5] = true := by decide +kernel
theorem subd17_1_970 : subd17_1 [2, 0, -4] = true := by decide +kernel
theorem subd17_1_971 : subd17_1 [2, 0, -3] = true := by decide +kernel
theorem subd17_1_972 : subd17_1 [2, 0, -2] = true := by decide +kernel
theorem subd17_1_973 : subd17_1 [2, 0, -1] = true := by decide +kernel
theorem subd17_1_974 : subd17_1 [2, 0, 0] = true := by decide +kernel
theorem subd17_1_975 : subd17_1 [2, 0, 1] = true := by decide +kernel
theorem subd17_1_976 : subd17_1 [2, 0, 2] = true := by decide +kernel
theorem subd17_1_977 : subd17_1 [2, 0, 3] = true := by decide +kernel
theorem subd17_1_978 : subd17_1 [2, 0, 4] = true := by decide +kernel
theorem subd17_1_979 : subd17_1 [2, 0, 5] = true := by decide +kernel
theorem subd17_1_980 : subd17_1 [2, 0, 6] = true := by decide +kernel
theorem subd17_1_981 : subd17_1 [2, 0, 7] = true := by decide +kernel
theorem subd17_1_982 : subd17_1 [2, 0, 8] = true := by decide +kernel
theorem subd17_1_983 : subd17_1 [2, 1, -8] = true := by decide +kernel
theorem subd17_1_984 : subd17_1 [2, 1, -7] = true := by decide +kernel
theorem subd17_1_985 : subd17_1 [2, 1, -6] = true := by decide +kernel
theorem subd17_1_986 : subd17_1 [2, 1, -5] = true := by decide +kernel
theorem subd17_1_987 : subd17_1 [2, 1, -4] = true := by decide +kernel
theorem subd17_1_988 : subd17_1 [2, 1, -3] = true := by decide +kernel
theorem subd17_1_989 : subd17_1 [2, 1, -2] = true := by decide +kernel
theorem subd17_1_990 : subd17_1 [2, 1, -1] = true := by decide +kernel
theorem subd17_1_991 : subd17_1 [2, 1, 0] = true := by decide +kernel
theorem sbd17_1_30 : ∀ q ∈ blkd17_1_30, subd17_1 q = true := by
  unfold blkd17_1_30
  exact List.forall_mem_cons.2 ⟨subd17_1_960, List.forall_mem_cons.2 ⟨subd17_1_961, List.forall_mem_cons.2 ⟨subd17_1_962, List.forall_mem_cons.2 ⟨subd17_1_963, List.forall_mem_cons.2 ⟨subd17_1_964, List.forall_mem_cons.2 ⟨subd17_1_965, List.forall_mem_cons.2 ⟨subd17_1_966, List.forall_mem_cons.2 ⟨subd17_1_967, List.forall_mem_cons.2 ⟨subd17_1_968, List.forall_mem_cons.2 ⟨subd17_1_969, List.forall_mem_cons.2 ⟨subd17_1_970, List.forall_mem_cons.2 ⟨subd17_1_971, List.forall_mem_cons.2 ⟨subd17_1_972, List.forall_mem_cons.2 ⟨subd17_1_973, List.forall_mem_cons.2 ⟨subd17_1_974, List.forall_mem_cons.2 ⟨subd17_1_975, List.forall_mem_cons.2 ⟨subd17_1_976, List.forall_mem_cons.2 ⟨subd17_1_977, List.forall_mem_cons.2 ⟨subd17_1_978, List.forall_mem_cons.2 ⟨subd17_1_979, List.forall_mem_cons.2 ⟨subd17_1_980, List.forall_mem_cons.2 ⟨subd17_1_981, List.forall_mem_cons.2 ⟨subd17_1_982, List.forall_mem_cons.2 ⟨subd17_1_983, List.forall_mem_cons.2 ⟨subd17_1_984, List.forall_mem_cons.2 ⟨subd17_1_985, List.forall_mem_cons.2 ⟨subd17_1_986, List.forall_mem_cons.2 ⟨subd17_1_987, List.forall_mem_cons.2 ⟨subd17_1_988, List.forall_mem_cons.2 ⟨subd17_1_989, List.forall_mem_cons.2 ⟨subd17_1_990, List.forall_mem_cons.2 ⟨subd17_1_991, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_1_992 : subd17_1 [2, 1, 1] = true := by decide +kernel
theorem subd17_1_993 : subd17_1 [2, 1, 2] = true := by decide +kernel
theorem subd17_1_994 : subd17_1 [2, 1, 3] = true := by decide +kernel
theorem subd17_1_995 : subd17_1 [2, 1, 4] = true := by decide +kernel
theorem subd17_1_996 : subd17_1 [2, 1, 5] = true := by decide +kernel
theorem subd17_1_997 : subd17_1 [2, 1, 6] = true := by decide +kernel
theorem subd17_1_998 : subd17_1 [2, 1, 7] = true := by decide +kernel
theorem subd17_1_999 : subd17_1 [2, 1, 8] = true := by decide +kernel
theorem subd17_1_1000 : subd17_1 [2, 2, -8] = true := by decide +kernel
theorem subd17_1_1001 : subd17_1 [2, 2, -7] = true := by decide +kernel
theorem subd17_1_1002 : subd17_1 [2, 2, -6] = true := by decide +kernel
theorem subd17_1_1003 : subd17_1 [2, 2, -5] = true := by decide +kernel
theorem subd17_1_1004 : subd17_1 [2, 2, -4] = true := by decide +kernel
theorem subd17_1_1005 : subd17_1 [2, 2, -3] = true := by decide +kernel
theorem subd17_1_1006 : subd17_1 [2, 2, -2] = true := by decide +kernel
theorem subd17_1_1007 : subd17_1 [2, 2, -1] = true := by decide +kernel
theorem subd17_1_1008 : subd17_1 [2, 2, 0] = true := by decide +kernel
theorem subd17_1_1009 : subd17_1 [2, 2, 1] = true := by decide +kernel
theorem subd17_1_1010 : subd17_1 [2, 2, 2] = true := by decide +kernel
theorem subd17_1_1011 : subd17_1 [2, 2, 3] = true := by decide +kernel
theorem subd17_1_1012 : subd17_1 [2, 2, 4] = true := by decide +kernel
theorem subd17_1_1013 : subd17_1 [2, 2, 5] = true := by decide +kernel
theorem subd17_1_1014 : subd17_1 [2, 2, 6] = true := by decide +kernel
theorem subd17_1_1015 : subd17_1 [2, 2, 7] = true := by decide +kernel
theorem subd17_1_1016 : subd17_1 [2, 2, 8] = true := by decide +kernel
theorem subd17_1_1017 : subd17_1 [2, 3, -7] = true := by decide +kernel
theorem subd17_1_1018 : subd17_1 [2, 3, -6] = true := by decide +kernel
theorem subd17_1_1019 : subd17_1 [2, 3, -5] = true := by decide +kernel
theorem subd17_1_1020 : subd17_1 [2, 3, -4] = true := by decide +kernel
theorem subd17_1_1021 : subd17_1 [2, 3, -3] = true := by decide +kernel
theorem subd17_1_1022 : subd17_1 [2, 3, -2] = true := by decide +kernel
theorem subd17_1_1023 : subd17_1 [2, 3, -1] = true := by decide +kernel
theorem sbd17_1_31 : ∀ q ∈ blkd17_1_31, subd17_1 q = true := by
  unfold blkd17_1_31
  exact List.forall_mem_cons.2 ⟨subd17_1_992, List.forall_mem_cons.2 ⟨subd17_1_993, List.forall_mem_cons.2 ⟨subd17_1_994, List.forall_mem_cons.2 ⟨subd17_1_995, List.forall_mem_cons.2 ⟨subd17_1_996, List.forall_mem_cons.2 ⟨subd17_1_997, List.forall_mem_cons.2 ⟨subd17_1_998, List.forall_mem_cons.2 ⟨subd17_1_999, List.forall_mem_cons.2 ⟨subd17_1_1000, List.forall_mem_cons.2 ⟨subd17_1_1001, List.forall_mem_cons.2 ⟨subd17_1_1002, List.forall_mem_cons.2 ⟨subd17_1_1003, List.forall_mem_cons.2 ⟨subd17_1_1004, List.forall_mem_cons.2 ⟨subd17_1_1005, List.forall_mem_cons.2 ⟨subd17_1_1006, List.forall_mem_cons.2 ⟨subd17_1_1007, List.forall_mem_cons.2 ⟨subd17_1_1008, List.forall_mem_cons.2 ⟨subd17_1_1009, List.forall_mem_cons.2 ⟨subd17_1_1010, List.forall_mem_cons.2 ⟨subd17_1_1011, List.forall_mem_cons.2 ⟨subd17_1_1012, List.forall_mem_cons.2 ⟨subd17_1_1013, List.forall_mem_cons.2 ⟨subd17_1_1014, List.forall_mem_cons.2 ⟨subd17_1_1015, List.forall_mem_cons.2 ⟨subd17_1_1016, List.forall_mem_cons.2 ⟨subd17_1_1017, List.forall_mem_cons.2 ⟨subd17_1_1018, List.forall_mem_cons.2 ⟨subd17_1_1019, List.forall_mem_cons.2 ⟨subd17_1_1020, List.forall_mem_cons.2 ⟨subd17_1_1021, List.forall_mem_cons.2 ⟨subd17_1_1022, List.forall_mem_cons.2 ⟨subd17_1_1023, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_1_1024 : subd17_1 [2, 3, 0] = true := by decide +kernel
theorem subd17_1_1025 : subd17_1 [2, 3, 1] = true := by decide +kernel
theorem subd17_1_1026 : subd17_1 [2, 3, 2] = true := by decide +kernel
theorem subd17_1_1027 : subd17_1 [2, 3, 3] = true := by decide +kernel
theorem subd17_1_1028 : subd17_1 [2, 3, 4] = true := by decide +kernel
theorem subd17_1_1029 : subd17_1 [2, 3, 5] = true := by decide +kernel
theorem subd17_1_1030 : subd17_1 [2, 3, 6] = true := by decide +kernel
theorem subd17_1_1031 : subd17_1 [2, 3, 7] = true := by decide +kernel
theorem subd17_1_1032 : subd17_1 [2, 4] = true := by decide +kernel
theorem subd17_1_1033 : subd17_1 [2, 5] = true := by decide +kernel
theorem subd17_1_1034 : subd17_1 [3, -7] = true := by decide +kernel
theorem subd17_1_1035 : subd17_1 [3, -6] = true := by decide +kernel
theorem subd17_1_1036 : subd17_1 [3, -5] = true := by decide +kernel
theorem subd17_1_1037 : subd17_1 [3, -4, -6] = true := by decide +kernel
theorem subd17_1_1038 : subd17_1 [3, -4, -5] = true := by decide +kernel
theorem subd17_1_1039 : subd17_1 [3, -4, -4] = true := by decide +kernel
theorem subd17_1_1040 : subd17_1 [3, -4, -3] = true := by decide +kernel
theorem subd17_1_1041 : subd17_1 [3, -4, -2] = true := by decide +kernel
theorem subd17_1_1042 : subd17_1 [3, -4, -1] = true := by decide +kernel
theorem subd17_1_1043 : subd17_1 [3, -4, 0] = true := by decide +kernel
theorem subd17_1_1044 : subd17_1 [3, -4, 1] = true := by decide +kernel
theorem subd17_1_1045 : subd17_1 [3, -4, 2] = true := by decide +kernel
theorem subd17_1_1046 : subd17_1 [3, -4, 3] = true := by decide +kernel
theorem subd17_1_1047 : subd17_1 [3, -4, 4] = true := by decide +kernel
theorem subd17_1_1048 : subd17_1 [3, -4, 5] = true := by decide +kernel
theorem subd17_1_1049 : subd17_1 [3, -4, 6] = true := by decide +kernel
theorem subd17_1_1050 : subd17_1 [3, -4, 7] = true := by decide +kernel
theorem subd17_1_1051 : subd17_1 [3, -3, -7] = true := by decide +kernel
theorem subd17_1_1052 : subd17_1 [3, -3, -6] = true := by decide +kernel
theorem subd17_1_1053 : subd17_1 [3, -3, -5] = true := by decide +kernel
theorem subd17_1_1054 : subd17_1 [3, -3, -4] = true := by decide +kernel
theorem subd17_1_1055 : subd17_1 [3, -3, -3] = true := by decide +kernel
theorem sbd17_1_32 : ∀ q ∈ blkd17_1_32, subd17_1 q = true := by
  unfold blkd17_1_32
  exact List.forall_mem_cons.2 ⟨subd17_1_1024, List.forall_mem_cons.2 ⟨subd17_1_1025, List.forall_mem_cons.2 ⟨subd17_1_1026, List.forall_mem_cons.2 ⟨subd17_1_1027, List.forall_mem_cons.2 ⟨subd17_1_1028, List.forall_mem_cons.2 ⟨subd17_1_1029, List.forall_mem_cons.2 ⟨subd17_1_1030, List.forall_mem_cons.2 ⟨subd17_1_1031, List.forall_mem_cons.2 ⟨subd17_1_1032, List.forall_mem_cons.2 ⟨subd17_1_1033, List.forall_mem_cons.2 ⟨subd17_1_1034, List.forall_mem_cons.2 ⟨subd17_1_1035, List.forall_mem_cons.2 ⟨subd17_1_1036, List.forall_mem_cons.2 ⟨subd17_1_1037, List.forall_mem_cons.2 ⟨subd17_1_1038, List.forall_mem_cons.2 ⟨subd17_1_1039, List.forall_mem_cons.2 ⟨subd17_1_1040, List.forall_mem_cons.2 ⟨subd17_1_1041, List.forall_mem_cons.2 ⟨subd17_1_1042, List.forall_mem_cons.2 ⟨subd17_1_1043, List.forall_mem_cons.2 ⟨subd17_1_1044, List.forall_mem_cons.2 ⟨subd17_1_1045, List.forall_mem_cons.2 ⟨subd17_1_1046, List.forall_mem_cons.2 ⟨subd17_1_1047, List.forall_mem_cons.2 ⟨subd17_1_1048, List.forall_mem_cons.2 ⟨subd17_1_1049, List.forall_mem_cons.2 ⟨subd17_1_1050, List.forall_mem_cons.2 ⟨subd17_1_1051, List.forall_mem_cons.2 ⟨subd17_1_1052, List.forall_mem_cons.2 ⟨subd17_1_1053, List.forall_mem_cons.2 ⟨subd17_1_1054, List.forall_mem_cons.2 ⟨subd17_1_1055, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_1_1056 : subd17_1 [3, -3, -2] = true := by decide +kernel
theorem subd17_1_1057 : subd17_1 [3, -3, -1] = true := by decide +kernel
theorem subd17_1_1058 : subd17_1 [3, -3, 0] = true := by decide +kernel
theorem subd17_1_1059 : subd17_1 [3, -3, 1] = true := by decide +kernel
theorem subd17_1_1060 : subd17_1 [3, -3, 2] = true := by decide +kernel
theorem subd17_1_1061 : subd17_1 [3, -3, 3] = true := by decide +kernel
theorem subd17_1_1062 : subd17_1 [3, -3, 4] = true := by decide +kernel
theorem subd17_1_1063 : subd17_1 [3, -3, 5] = true := by decide +kernel
theorem subd17_1_1064 : subd17_1 [3, -3, 6] = true := by decide +kernel
theorem subd17_1_1065 : subd17_1 [3, -3, 7] = true := by decide +kernel
theorem subd17_1_1066 : subd17_1 [3, -3, 8] = true := by decide +kernel
theorem subd17_1_1067 : subd17_1 [3, -2, -7] = true := by decide +kernel
theorem subd17_1_1068 : subd17_1 [3, -2, -6] = true := by decide +kernel
theorem subd17_1_1069 : subd17_1 [3, -2, -5] = true := by decide +kernel
theorem subd17_1_1070 : subd17_1 [3, -2, -4] = true := by decide +kernel
theorem subd17_1_1071 : subd17_1 [3, -2, -3] = true := by decide +kernel
theorem subd17_1_1072 : subd17_1 [3, -2, -2] = true := by decide +kernel
theorem subd17_1_1073 : subd17_1 [3, -2, -1] = true := by decide +kernel
theorem subd17_1_1074 : subd17_1 [3, -2, 0] = true := by decide +kernel
theorem subd17_1_1075 : subd17_1 [3, -2, 1] = true := by decide +kernel
theorem subd17_1_1076 : subd17_1 [3, -2, 2] = true := by decide +kernel
theorem subd17_1_1077 : subd17_1 [3, -2, 3] = true := by decide +kernel
theorem subd17_1_1078 : subd17_1 [3, -2, 4] = true := by decide +kernel
theorem subd17_1_1079 : subd17_1 [3, -2, 5] = true := by decide +kernel
theorem subd17_1_1080 : subd17_1 [3, -2, 6] = true := by decide +kernel
theorem subd17_1_1081 : subd17_1 [3, -2, 7] = true := by decide +kernel
theorem subd17_1_1082 : subd17_1 [3, -2, 8] = true := by decide +kernel
theorem subd17_1_1083 : subd17_1 [3, -1, -7] = true := by decide +kernel
theorem subd17_1_1084 : subd17_1 [3, -1, -6] = true := by decide +kernel
theorem subd17_1_1085 : subd17_1 [3, -1, -5] = true := by decide +kernel
theorem subd17_1_1086 : subd17_1 [3, -1, -4] = true := by decide +kernel
theorem subd17_1_1087 : subd17_1 [3, -1, -3] = true := by decide +kernel
theorem sbd17_1_33 : ∀ q ∈ blkd17_1_33, subd17_1 q = true := by
  unfold blkd17_1_33
  exact List.forall_mem_cons.2 ⟨subd17_1_1056, List.forall_mem_cons.2 ⟨subd17_1_1057, List.forall_mem_cons.2 ⟨subd17_1_1058, List.forall_mem_cons.2 ⟨subd17_1_1059, List.forall_mem_cons.2 ⟨subd17_1_1060, List.forall_mem_cons.2 ⟨subd17_1_1061, List.forall_mem_cons.2 ⟨subd17_1_1062, List.forall_mem_cons.2 ⟨subd17_1_1063, List.forall_mem_cons.2 ⟨subd17_1_1064, List.forall_mem_cons.2 ⟨subd17_1_1065, List.forall_mem_cons.2 ⟨subd17_1_1066, List.forall_mem_cons.2 ⟨subd17_1_1067, List.forall_mem_cons.2 ⟨subd17_1_1068, List.forall_mem_cons.2 ⟨subd17_1_1069, List.forall_mem_cons.2 ⟨subd17_1_1070, List.forall_mem_cons.2 ⟨subd17_1_1071, List.forall_mem_cons.2 ⟨subd17_1_1072, List.forall_mem_cons.2 ⟨subd17_1_1073, List.forall_mem_cons.2 ⟨subd17_1_1074, List.forall_mem_cons.2 ⟨subd17_1_1075, List.forall_mem_cons.2 ⟨subd17_1_1076, List.forall_mem_cons.2 ⟨subd17_1_1077, List.forall_mem_cons.2 ⟨subd17_1_1078, List.forall_mem_cons.2 ⟨subd17_1_1079, List.forall_mem_cons.2 ⟨subd17_1_1080, List.forall_mem_cons.2 ⟨subd17_1_1081, List.forall_mem_cons.2 ⟨subd17_1_1082, List.forall_mem_cons.2 ⟨subd17_1_1083, List.forall_mem_cons.2 ⟨subd17_1_1084, List.forall_mem_cons.2 ⟨subd17_1_1085, List.forall_mem_cons.2 ⟨subd17_1_1086, List.forall_mem_cons.2 ⟨subd17_1_1087, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_1_1088 : subd17_1 [3, -1, -2] = true := by decide +kernel
theorem subd17_1_1089 : subd17_1 [3, -1, -1] = true := by decide +kernel
theorem subd17_1_1090 : subd17_1 [3, -1, 0] = true := by decide +kernel
theorem subd17_1_1091 : subd17_1 [3, -1, 1] = true := by decide +kernel
theorem subd17_1_1092 : subd17_1 [3, -1, 2] = true := by decide +kernel
theorem subd17_1_1093 : subd17_1 [3, -1, 3] = true := by decide +kernel
theorem subd17_1_1094 : subd17_1 [3, -1, 4] = true := by decide +kernel
theorem subd17_1_1095 : subd17_1 [3, -1, 5] = true := by decide +kernel
theorem subd17_1_1096 : subd17_1 [3, -1, 6] = true := by decide +kernel
theorem subd17_1_1097 : subd17_1 [3, -1, 7] = true := by decide +kernel
theorem subd17_1_1098 : subd17_1 [3, -1, 8] = true := by decide +kernel
theorem subd17_1_1099 : subd17_1 [3, 0, -7] = true := by decide +kernel
theorem subd17_1_1100 : subd17_1 [3, 0, -6] = true := by decide +kernel
theorem subd17_1_1101 : subd17_1 [3, 0, -5] = true := by decide +kernel
theorem subd17_1_1102 : subd17_1 [3, 0, -4] = true := by decide +kernel
theorem subd17_1_1103 : subd17_1 [3, 0, -3] = true := by decide +kernel
theorem subd17_1_1104 : subd17_1 [3, 0, -2] = true := by decide +kernel
theorem subd17_1_1105 : subd17_1 [3, 0, -1] = true := by decide +kernel
theorem subd17_1_1106 : subd17_1 [3, 0, 0] = true := by decide +kernel
theorem subd17_1_1107 : subd17_1 [3, 0, 1] = true := by decide +kernel
theorem subd17_1_1108 : subd17_1 [3, 0, 2] = true := by decide +kernel
theorem subd17_1_1109 : subd17_1 [3, 0, 3] = true := by decide +kernel
theorem subd17_1_1110 : subd17_1 [3, 0, 4] = true := by decide +kernel
theorem subd17_1_1111 : subd17_1 [3, 0, 5] = true := by decide +kernel
theorem subd17_1_1112 : subd17_1 [3, 0, 6] = true := by decide +kernel
theorem subd17_1_1113 : subd17_1 [3, 0, 7] = true := by decide +kernel
theorem subd17_1_1114 : subd17_1 [3, 0, 8] = true := by decide +kernel
theorem subd17_1_1115 : subd17_1 [3, 1, -7] = true := by decide +kernel
theorem subd17_1_1116 : subd17_1 [3, 1, -6] = true := by decide +kernel
theorem subd17_1_1117 : subd17_1 [3, 1, -5] = true := by decide +kernel
theorem subd17_1_1118 : subd17_1 [3, 1, -4] = true := by decide +kernel
theorem subd17_1_1119 : subd17_1 [3, 1, -3] = true := by decide +kernel
theorem sbd17_1_34 : ∀ q ∈ blkd17_1_34, subd17_1 q = true := by
  unfold blkd17_1_34
  exact List.forall_mem_cons.2 ⟨subd17_1_1088, List.forall_mem_cons.2 ⟨subd17_1_1089, List.forall_mem_cons.2 ⟨subd17_1_1090, List.forall_mem_cons.2 ⟨subd17_1_1091, List.forall_mem_cons.2 ⟨subd17_1_1092, List.forall_mem_cons.2 ⟨subd17_1_1093, List.forall_mem_cons.2 ⟨subd17_1_1094, List.forall_mem_cons.2 ⟨subd17_1_1095, List.forall_mem_cons.2 ⟨subd17_1_1096, List.forall_mem_cons.2 ⟨subd17_1_1097, List.forall_mem_cons.2 ⟨subd17_1_1098, List.forall_mem_cons.2 ⟨subd17_1_1099, List.forall_mem_cons.2 ⟨subd17_1_1100, List.forall_mem_cons.2 ⟨subd17_1_1101, List.forall_mem_cons.2 ⟨subd17_1_1102, List.forall_mem_cons.2 ⟨subd17_1_1103, List.forall_mem_cons.2 ⟨subd17_1_1104, List.forall_mem_cons.2 ⟨subd17_1_1105, List.forall_mem_cons.2 ⟨subd17_1_1106, List.forall_mem_cons.2 ⟨subd17_1_1107, List.forall_mem_cons.2 ⟨subd17_1_1108, List.forall_mem_cons.2 ⟨subd17_1_1109, List.forall_mem_cons.2 ⟨subd17_1_1110, List.forall_mem_cons.2 ⟨subd17_1_1111, List.forall_mem_cons.2 ⟨subd17_1_1112, List.forall_mem_cons.2 ⟨subd17_1_1113, List.forall_mem_cons.2 ⟨subd17_1_1114, List.forall_mem_cons.2 ⟨subd17_1_1115, List.forall_mem_cons.2 ⟨subd17_1_1116, List.forall_mem_cons.2 ⟨subd17_1_1117, List.forall_mem_cons.2 ⟨subd17_1_1118, List.forall_mem_cons.2 ⟨subd17_1_1119, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_1_1120 : subd17_1 [3, 1, -2] = true := by decide +kernel
theorem subd17_1_1121 : subd17_1 [3, 1, -1] = true := by decide +kernel
theorem subd17_1_1122 : subd17_1 [3, 1, 0] = true := by decide +kernel
theorem subd17_1_1123 : subd17_1 [3, 1, 1] = true := by decide +kernel
theorem subd17_1_1124 : subd17_1 [3, 1, 2] = true := by decide +kernel
theorem subd17_1_1125 : subd17_1 [3, 1, 3] = true := by decide +kernel
theorem subd17_1_1126 : subd17_1 [3, 1, 4] = true := by decide +kernel
theorem subd17_1_1127 : subd17_1 [3, 1, 5] = true := by decide +kernel
theorem subd17_1_1128 : subd17_1 [3, 1, 6] = true := by decide +kernel
theorem subd17_1_1129 : subd17_1 [3, 1, 7] = true := by decide +kernel
theorem subd17_1_1130 : subd17_1 [3, 1, 8] = true := by decide +kernel
theorem subd17_1_1131 : subd17_1 [3, 2, -6] = true := by decide +kernel
theorem subd17_1_1132 : subd17_1 [3, 2, -5] = true := by decide +kernel
theorem subd17_1_1133 : subd17_1 [3, 2, -4] = true := by decide +kernel
theorem subd17_1_1134 : subd17_1 [3, 2, -3] = true := by decide +kernel
theorem subd17_1_1135 : subd17_1 [3, 2, -2] = true := by decide +kernel
theorem subd17_1_1136 : subd17_1 [3, 2, -1] = true := by decide +kernel
theorem subd17_1_1137 : subd17_1 [3, 2, 0] = true := by decide +kernel
theorem subd17_1_1138 : subd17_1 [3, 2, 1] = true := by decide +kernel
theorem subd17_1_1139 : subd17_1 [3, 2, 2] = true := by decide +kernel
theorem subd17_1_1140 : subd17_1 [3, 2, 3] = true := by decide +kernel
theorem subd17_1_1141 : subd17_1 [3, 2, 4] = true := by decide +kernel
theorem subd17_1_1142 : subd17_1 [3, 2, 5] = true := by decide +kernel
theorem subd17_1_1143 : subd17_1 [3, 2, 6] = true := by decide +kernel
theorem subd17_1_1144 : subd17_1 [3, 2, 7] = true := by decide +kernel
theorem subd17_1_1145 : subd17_1 [3, 3] = true := by decide +kernel
theorem subd17_1_1146 : subd17_1 [3, 4] = true := by decide +kernel
theorem subd17_1_1147 : subd17_1 [3, 5] = true := by decide +kernel
theorem subd17_1_1148 : subd17_1 [4, -7] = true := by decide +kernel
theorem subd17_1_1149 : subd17_1 [4, -6] = true := by decide +kernel
theorem subd17_1_1150 : subd17_1 [4, -5] = true := by decide +kernel
theorem subd17_1_1151 : subd17_1 [4, -4] = true := by decide +kernel
theorem sbd17_1_35 : ∀ q ∈ blkd17_1_35, subd17_1 q = true := by
  unfold blkd17_1_35
  exact List.forall_mem_cons.2 ⟨subd17_1_1120, List.forall_mem_cons.2 ⟨subd17_1_1121, List.forall_mem_cons.2 ⟨subd17_1_1122, List.forall_mem_cons.2 ⟨subd17_1_1123, List.forall_mem_cons.2 ⟨subd17_1_1124, List.forall_mem_cons.2 ⟨subd17_1_1125, List.forall_mem_cons.2 ⟨subd17_1_1126, List.forall_mem_cons.2 ⟨subd17_1_1127, List.forall_mem_cons.2 ⟨subd17_1_1128, List.forall_mem_cons.2 ⟨subd17_1_1129, List.forall_mem_cons.2 ⟨subd17_1_1130, List.forall_mem_cons.2 ⟨subd17_1_1131, List.forall_mem_cons.2 ⟨subd17_1_1132, List.forall_mem_cons.2 ⟨subd17_1_1133, List.forall_mem_cons.2 ⟨subd17_1_1134, List.forall_mem_cons.2 ⟨subd17_1_1135, List.forall_mem_cons.2 ⟨subd17_1_1136, List.forall_mem_cons.2 ⟨subd17_1_1137, List.forall_mem_cons.2 ⟨subd17_1_1138, List.forall_mem_cons.2 ⟨subd17_1_1139, List.forall_mem_cons.2 ⟨subd17_1_1140, List.forall_mem_cons.2 ⟨subd17_1_1141, List.forall_mem_cons.2 ⟨subd17_1_1142, List.forall_mem_cons.2 ⟨subd17_1_1143, List.forall_mem_cons.2 ⟨subd17_1_1144, List.forall_mem_cons.2 ⟨subd17_1_1145, List.forall_mem_cons.2 ⟨subd17_1_1146, List.forall_mem_cons.2 ⟨subd17_1_1147, List.forall_mem_cons.2 ⟨subd17_1_1148, List.forall_mem_cons.2 ⟨subd17_1_1149, List.forall_mem_cons.2 ⟨subd17_1_1150, List.forall_mem_cons.2 ⟨subd17_1_1151, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_1_1152 : subd17_1 [4, -3, -6] = true := by decide +kernel
theorem subd17_1_1153 : subd17_1 [4, -3, -5] = true := by decide +kernel
theorem subd17_1_1154 : subd17_1 [4, -3, -4] = true := by decide +kernel
theorem subd17_1_1155 : subd17_1 [4, -3, -3] = true := by decide +kernel
theorem subd17_1_1156 : subd17_1 [4, -3, -2] = true := by decide +kernel
theorem subd17_1_1157 : subd17_1 [4, -3, -1] = true := by decide +kernel
theorem subd17_1_1158 : subd17_1 [4, -3, 0] = true := by decide +kernel
theorem subd17_1_1159 : subd17_1 [4, -3, 1] = true := by decide +kernel
theorem subd17_1_1160 : subd17_1 [4, -3, 2] = true := by decide +kernel
theorem subd17_1_1161 : subd17_1 [4, -3, 3] = true := by decide +kernel
theorem subd17_1_1162 : subd17_1 [4, -3, 4] = true := by decide +kernel
theorem subd17_1_1163 : subd17_1 [4, -3, 5] = true := by decide +kernel
theorem subd17_1_1164 : subd17_1 [4, -3, 6] = true := by decide +kernel
theorem subd17_1_1165 : subd17_1 [4, -3, 7] = true := by decide +kernel
theorem subd17_1_1166 : subd17_1 [4, -2, -6] = true := by decide +kernel
theorem subd17_1_1167 : subd17_1 [4, -2, -5] = true := by decide +kernel
theorem subd17_1_1168 : subd17_1 [4, -2, -4] = true := by decide +kernel
theorem subd17_1_1169 : subd17_1 [4, -2, -3] = true := by decide +kernel
theorem subd17_1_1170 : subd17_1 [4, -2, -2] = true := by decide +kernel
theorem subd17_1_1171 : subd17_1 [4, -2, -1] = true := by decide +kernel
theorem subd17_1_1172 : subd17_1 [4, -2, 0] = true := by decide +kernel
theorem subd17_1_1173 : subd17_1 [4, -2, 1] = true := by decide +kernel
theorem subd17_1_1174 : subd17_1 [4, -2, 2] = true := by decide +kernel
theorem subd17_1_1175 : subd17_1 [4, -2, 3] = true := by decide +kernel
theorem subd17_1_1176 : subd17_1 [4, -2, 4] = true := by decide +kernel
theorem subd17_1_1177 : subd17_1 [4, -2, 5] = true := by decide +kernel
theorem subd17_1_1178 : subd17_1 [4, -2, 6] = true := by decide +kernel
theorem subd17_1_1179 : subd17_1 [4, -2, 7] = true := by decide +kernel
theorem subd17_1_1180 : subd17_1 [4, -1, -6] = true := by decide +kernel
theorem subd17_1_1181 : subd17_1 [4, -1, -5] = true := by decide +kernel
theorem subd17_1_1182 : subd17_1 [4, -1, -4] = true := by decide +kernel
theorem subd17_1_1183 : subd17_1 [4, -1, -3] = true := by decide +kernel
theorem sbd17_1_36 : ∀ q ∈ blkd17_1_36, subd17_1 q = true := by
  unfold blkd17_1_36
  exact List.forall_mem_cons.2 ⟨subd17_1_1152, List.forall_mem_cons.2 ⟨subd17_1_1153, List.forall_mem_cons.2 ⟨subd17_1_1154, List.forall_mem_cons.2 ⟨subd17_1_1155, List.forall_mem_cons.2 ⟨subd17_1_1156, List.forall_mem_cons.2 ⟨subd17_1_1157, List.forall_mem_cons.2 ⟨subd17_1_1158, List.forall_mem_cons.2 ⟨subd17_1_1159, List.forall_mem_cons.2 ⟨subd17_1_1160, List.forall_mem_cons.2 ⟨subd17_1_1161, List.forall_mem_cons.2 ⟨subd17_1_1162, List.forall_mem_cons.2 ⟨subd17_1_1163, List.forall_mem_cons.2 ⟨subd17_1_1164, List.forall_mem_cons.2 ⟨subd17_1_1165, List.forall_mem_cons.2 ⟨subd17_1_1166, List.forall_mem_cons.2 ⟨subd17_1_1167, List.forall_mem_cons.2 ⟨subd17_1_1168, List.forall_mem_cons.2 ⟨subd17_1_1169, List.forall_mem_cons.2 ⟨subd17_1_1170, List.forall_mem_cons.2 ⟨subd17_1_1171, List.forall_mem_cons.2 ⟨subd17_1_1172, List.forall_mem_cons.2 ⟨subd17_1_1173, List.forall_mem_cons.2 ⟨subd17_1_1174, List.forall_mem_cons.2 ⟨subd17_1_1175, List.forall_mem_cons.2 ⟨subd17_1_1176, List.forall_mem_cons.2 ⟨subd17_1_1177, List.forall_mem_cons.2 ⟨subd17_1_1178, List.forall_mem_cons.2 ⟨subd17_1_1179, List.forall_mem_cons.2 ⟨subd17_1_1180, List.forall_mem_cons.2 ⟨subd17_1_1181, List.forall_mem_cons.2 ⟨subd17_1_1182, List.forall_mem_cons.2 ⟨subd17_1_1183, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_1_1184 : subd17_1 [4, -1, -2] = true := by decide +kernel
theorem subd17_1_1185 : subd17_1 [4, -1, -1] = true := by decide +kernel
theorem subd17_1_1186 : subd17_1 [4, -1, 0] = true := by decide +kernel
theorem subd17_1_1187 : subd17_1 [4, -1, 1] = true := by decide +kernel
theorem subd17_1_1188 : subd17_1 [4, -1, 2] = true := by decide +kernel
theorem subd17_1_1189 : subd17_1 [4, -1, 3] = true := by decide +kernel
theorem subd17_1_1190 : subd17_1 [4, -1, 4] = true := by decide +kernel
theorem subd17_1_1191 : subd17_1 [4, -1, 5] = true := by decide +kernel
theorem subd17_1_1192 : subd17_1 [4, -1, 6] = true := by decide +kernel
theorem subd17_1_1193 : subd17_1 [4, -1, 7] = true := by decide +kernel
theorem subd17_1_1194 : subd17_1 [4, -1, 8] = true := by decide +kernel
theorem subd17_1_1195 : subd17_1 [4, 0, -6] = true := by decide +kernel
theorem subd17_1_1196 : subd17_1 [4, 0, -5] = true := by decide +kernel
theorem subd17_1_1197 : subd17_1 [4, 0, -4] = true := by decide +kernel
theorem subd17_1_1198 : subd17_1 [4, 0, -3] = true := by decide +kernel
theorem subd17_1_1199 : subd17_1 [4, 0, -2] = true := by decide +kernel
theorem subd17_1_1200 : subd17_1 [4, 0, -1] = true := by decide +kernel
theorem subd17_1_1201 : subd17_1 [4, 0, 0] = true := by decide +kernel
theorem subd17_1_1202 : subd17_1 [4, 0, 1] = true := by decide +kernel
theorem subd17_1_1203 : subd17_1 [4, 0, 2] = true := by decide +kernel
theorem subd17_1_1204 : subd17_1 [4, 0, 3] = true := by decide +kernel
theorem subd17_1_1205 : subd17_1 [4, 0, 4] = true := by decide +kernel
theorem subd17_1_1206 : subd17_1 [4, 0, 5] = true := by decide +kernel
theorem subd17_1_1207 : subd17_1 [4, 0, 6] = true := by decide +kernel
theorem subd17_1_1208 : subd17_1 [4, 0, 7] = true := by decide +kernel
theorem subd17_1_1209 : subd17_1 [4, 1, -5] = true := by decide +kernel
theorem subd17_1_1210 : subd17_1 [4, 1, -4] = true := by decide +kernel
theorem subd17_1_1211 : subd17_1 [4, 1, -3] = true := by decide +kernel
theorem subd17_1_1212 : subd17_1 [4, 1, -2] = true := by decide +kernel
theorem subd17_1_1213 : subd17_1 [4, 1, -1] = true := by decide +kernel
theorem subd17_1_1214 : subd17_1 [4, 1, 0] = true := by decide +kernel
theorem subd17_1_1215 : subd17_1 [4, 1, 1] = true := by decide +kernel
theorem sbd17_1_37 : ∀ q ∈ blkd17_1_37, subd17_1 q = true := by
  unfold blkd17_1_37
  exact List.forall_mem_cons.2 ⟨subd17_1_1184, List.forall_mem_cons.2 ⟨subd17_1_1185, List.forall_mem_cons.2 ⟨subd17_1_1186, List.forall_mem_cons.2 ⟨subd17_1_1187, List.forall_mem_cons.2 ⟨subd17_1_1188, List.forall_mem_cons.2 ⟨subd17_1_1189, List.forall_mem_cons.2 ⟨subd17_1_1190, List.forall_mem_cons.2 ⟨subd17_1_1191, List.forall_mem_cons.2 ⟨subd17_1_1192, List.forall_mem_cons.2 ⟨subd17_1_1193, List.forall_mem_cons.2 ⟨subd17_1_1194, List.forall_mem_cons.2 ⟨subd17_1_1195, List.forall_mem_cons.2 ⟨subd17_1_1196, List.forall_mem_cons.2 ⟨subd17_1_1197, List.forall_mem_cons.2 ⟨subd17_1_1198, List.forall_mem_cons.2 ⟨subd17_1_1199, List.forall_mem_cons.2 ⟨subd17_1_1200, List.forall_mem_cons.2 ⟨subd17_1_1201, List.forall_mem_cons.2 ⟨subd17_1_1202, List.forall_mem_cons.2 ⟨subd17_1_1203, List.forall_mem_cons.2 ⟨subd17_1_1204, List.forall_mem_cons.2 ⟨subd17_1_1205, List.forall_mem_cons.2 ⟨subd17_1_1206, List.forall_mem_cons.2 ⟨subd17_1_1207, List.forall_mem_cons.2 ⟨subd17_1_1208, List.forall_mem_cons.2 ⟨subd17_1_1209, List.forall_mem_cons.2 ⟨subd17_1_1210, List.forall_mem_cons.2 ⟨subd17_1_1211, List.forall_mem_cons.2 ⟨subd17_1_1212, List.forall_mem_cons.2 ⟨subd17_1_1213, List.forall_mem_cons.2 ⟨subd17_1_1214, List.forall_mem_cons.2 ⟨subd17_1_1215, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_1_1216 : subd17_1 [4, 1, 2] = true := by decide +kernel
theorem subd17_1_1217 : subd17_1 [4, 1, 3] = true := by decide +kernel
theorem subd17_1_1218 : subd17_1 [4, 1, 4] = true := by decide +kernel
theorem subd17_1_1219 : subd17_1 [4, 1, 5] = true := by decide +kernel
theorem subd17_1_1220 : subd17_1 [4, 1, 6] = true := by decide +kernel
theorem subd17_1_1221 : subd17_1 [4, 1, 7] = true := by decide +kernel
theorem subd17_1_1222 : subd17_1 [4, 2] = true := by decide +kernel
theorem subd17_1_1223 : subd17_1 [4, 3] = true := by decide +kernel
theorem subd17_1_1224 : subd17_1 [4, 4] = true := by decide +kernel
theorem subd17_1_1225 : subd17_1 [5, -6] = true := by decide +kernel
theorem subd17_1_1226 : subd17_1 [5, -5] = true := by decide +kernel
theorem subd17_1_1227 : subd17_1 [5, -4] = true := by decide +kernel
theorem subd17_1_1228 : subd17_1 [5, -3] = true := by decide +kernel
theorem subd17_1_1229 : subd17_1 [5, -2] = true := by decide +kernel
theorem subd17_1_1230 : subd17_1 [5, -1] = true := by decide +kernel
theorem subd17_1_1231 : subd17_1 [5, 0] = true := by decide +kernel
theorem subd17_1_1232 : subd17_1 [5, 1] = true := by decide +kernel
theorem subd17_1_1233 : subd17_1 [5, 2] = true := by decide +kernel
theorem subd17_1_1234 : subd17_1 [6] = true := by decide +kernel
theorem sbd17_1_38 : ∀ q ∈ blkd17_1_38, subd17_1 q = true := by
  unfold blkd17_1_38
  exact List.forall_mem_cons.2 ⟨subd17_1_1216, List.forall_mem_cons.2 ⟨subd17_1_1217, List.forall_mem_cons.2 ⟨subd17_1_1218, List.forall_mem_cons.2 ⟨subd17_1_1219, List.forall_mem_cons.2 ⟨subd17_1_1220, List.forall_mem_cons.2 ⟨subd17_1_1221, List.forall_mem_cons.2 ⟨subd17_1_1222, List.forall_mem_cons.2 ⟨subd17_1_1223, List.forall_mem_cons.2 ⟨subd17_1_1224, List.forall_mem_cons.2 ⟨subd17_1_1225, List.forall_mem_cons.2 ⟨subd17_1_1226, List.forall_mem_cons.2 ⟨subd17_1_1227, List.forall_mem_cons.2 ⟨subd17_1_1228, List.forall_mem_cons.2 ⟨subd17_1_1229, List.forall_mem_cons.2 ⟨subd17_1_1230, List.forall_mem_cons.2 ⟨subd17_1_1231, List.forall_mem_cons.2 ⟨subd17_1_1232, List.forall_mem_cons.2 ⟨subd17_1_1233, List.forall_mem_cons.2 ⟨subd17_1_1234, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd17_2 : ldCheck G d17_2.U d17_2.ms ldd17_2 = true := by decide +kernel
theorem pre_okd17_2 : subPre G cell17 d17_2 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C143
