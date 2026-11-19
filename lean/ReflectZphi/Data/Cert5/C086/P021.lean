import ReflectZphi.Data.Cert5.C086.Base

namespace ReflectZphi.Data.Cert5.C086
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub7_992 : sub7 [4, -6] = true := by decide +kernel
theorem sub7_993 : sub7 [4, -5] = true := by decide +kernel
theorem sub7_994 : sub7 [4, -4] = true := by decide +kernel
theorem sub7_995 : sub7 [4, -3] = true := by decide +kernel
theorem sub7_996 : sub7 [4, -2] = true := by decide +kernel
theorem sub7_997 : sub7 [4, -1, -8] = true := by decide +kernel
theorem sub7_998 : sub7 [4, -1, -7] = true := by decide +kernel
theorem sub7_999 : sub7 [4, -1, -6] = true := by decide +kernel
theorem sub7_1000 : sub7 [4, -1, -5] = true := by decide +kernel
theorem sub7_1001 : sub7 [4, -1, -4] = true := by decide +kernel
theorem sub7_1002 : sub7 [4, -1, -3] = true := by decide +kernel
theorem sub7_1003 : sub7 [4, -1, -2] = true := by decide +kernel
theorem sub7_1004 : sub7 [4, -1, -1] = true := by decide +kernel
theorem sub7_1005 : sub7 [4, -1, 0] = true := by decide +kernel
theorem sub7_1006 : sub7 [4, -1, 1] = true := by decide +kernel
theorem sub7_1007 : sub7 [4, -1, 2] = true := by decide +kernel
theorem sub7_1008 : sub7 [4, -1, 3] = true := by decide +kernel
theorem sub7_1009 : sub7 [4, -1, 4] = true := by decide +kernel
theorem sub7_1010 : sub7 [4, -1, 5] = true := by decide +kernel
theorem sub7_1011 : sub7 [4, 0, -8] = true := by decide +kernel
theorem sub7_1012 : sub7 [4, 0, -7] = true := by decide +kernel
theorem sub7_1013 : sub7 [4, 0, -6] = true := by decide +kernel
theorem sub7_1014 : sub7 [4, 0, -5] = true := by decide +kernel
theorem sub7_1015 : sub7 [4, 0, -4] = true := by decide +kernel
theorem sub7_1016 : sub7 [4, 0, -3] = true := by decide +kernel
theorem sub7_1017 : sub7 [4, 0, -2] = true := by decide +kernel
theorem sub7_1018 : sub7 [4, 0, -1] = true := by decide +kernel
theorem sub7_1019 : sub7 [4, 0, 0] = true := by decide +kernel
theorem sub7_1020 : sub7 [4, 0, 1] = true := by decide +kernel
theorem sub7_1021 : sub7 [4, 0, 2] = true := by decide +kernel
theorem sub7_1022 : sub7 [4, 0, 3] = true := by decide +kernel
theorem sub7_1023 : sub7 [4, 0, 4] = true := by decide +kernel
theorem sb7_31 : ∀ q ∈ blk7_31, sub7 q = true := by
  unfold blk7_31
  exact List.forall_mem_cons.2 ⟨sub7_992, List.forall_mem_cons.2 ⟨sub7_993, List.forall_mem_cons.2 ⟨sub7_994, List.forall_mem_cons.2 ⟨sub7_995, List.forall_mem_cons.2 ⟨sub7_996, List.forall_mem_cons.2 ⟨sub7_997, List.forall_mem_cons.2 ⟨sub7_998, List.forall_mem_cons.2 ⟨sub7_999, List.forall_mem_cons.2 ⟨sub7_1000, List.forall_mem_cons.2 ⟨sub7_1001, List.forall_mem_cons.2 ⟨sub7_1002, List.forall_mem_cons.2 ⟨sub7_1003, List.forall_mem_cons.2 ⟨sub7_1004, List.forall_mem_cons.2 ⟨sub7_1005, List.forall_mem_cons.2 ⟨sub7_1006, List.forall_mem_cons.2 ⟨sub7_1007, List.forall_mem_cons.2 ⟨sub7_1008, List.forall_mem_cons.2 ⟨sub7_1009, List.forall_mem_cons.2 ⟨sub7_1010, List.forall_mem_cons.2 ⟨sub7_1011, List.forall_mem_cons.2 ⟨sub7_1012, List.forall_mem_cons.2 ⟨sub7_1013, List.forall_mem_cons.2 ⟨sub7_1014, List.forall_mem_cons.2 ⟨sub7_1015, List.forall_mem_cons.2 ⟨sub7_1016, List.forall_mem_cons.2 ⟨sub7_1017, List.forall_mem_cons.2 ⟨sub7_1018, List.forall_mem_cons.2 ⟨sub7_1019, List.forall_mem_cons.2 ⟨sub7_1020, List.forall_mem_cons.2 ⟨sub7_1021, List.forall_mem_cons.2 ⟨sub7_1022, List.forall_mem_cons.2 ⟨sub7_1023, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_1024 : sub7 [4, 0, 5] = true := by decide +kernel
theorem sub7_1025 : sub7 [4, 0, 6] = true := by decide +kernel
theorem sub7_1026 : sub7 [4, 1, -7] = true := by decide +kernel
theorem sub7_1027 : sub7 [4, 1, -6] = true := by decide +kernel
theorem sub7_1028 : sub7 [4, 1, -5] = true := by decide +kernel
theorem sub7_1029 : sub7 [4, 1, -4] = true := by decide +kernel
theorem sub7_1030 : sub7 [4, 1, -3] = true := by decide +kernel
theorem sub7_1031 : sub7 [4, 1, -2] = true := by decide +kernel
theorem sub7_1032 : sub7 [4, 1, -1] = true := by decide +kernel
theorem sub7_1033 : sub7 [4, 1, 0] = true := by decide +kernel
theorem sub7_1034 : sub7 [4, 1, 1] = true := by decide +kernel
theorem sub7_1035 : sub7 [4, 1, 2] = true := by decide +kernel
theorem sub7_1036 : sub7 [4, 1, 3] = true := by decide +kernel
theorem sub7_1037 : sub7 [4, 1, 4] = true := by decide +kernel
theorem sub7_1038 : sub7 [4, 1, 5] = true := by decide +kernel
theorem sub7_1039 : sub7 [4, 1, 6] = true := by decide +kernel
theorem sub7_1040 : sub7 [4, 2] = true := by decide +kernel
theorem sub7_1041 : sub7 [4, 3] = true := by decide +kernel
theorem sub7_1042 : sub7 [4, 4] = true := by decide +kernel
theorem sub7_1043 : sub7 [4, 5] = true := by decide +kernel
theorem sub7_1044 : sub7 [5, -5] = true := by decide +kernel
theorem sub7_1045 : sub7 [5, -4] = true := by decide +kernel
theorem sub7_1046 : sub7 [5, -3] = true := by decide +kernel
theorem sub7_1047 : sub7 [5, -2] = true := by decide +kernel
theorem sub7_1048 : sub7 [5, -1] = true := by decide +kernel
theorem sub7_1049 : sub7 [5, 0] = true := by decide +kernel
theorem sub7_1050 : sub7 [5, 1] = true := by decide +kernel
theorem sub7_1051 : sub7 [5, 2] = true := by decide +kernel
theorem sub7_1052 : sub7 [5, 3] = true := by decide +kernel
theorem sub7_1053 : sub7 [5, 4] = true := by decide +kernel
theorem sub7_1054 : sub7 [6, -3] = true := by decide +kernel
theorem sub7_1055 : sub7 [6, -2] = true := by decide +kernel
theorem sb7_32 : ∀ q ∈ blk7_32, sub7 q = true := by
  unfold blk7_32
  exact List.forall_mem_cons.2 ⟨sub7_1024, List.forall_mem_cons.2 ⟨sub7_1025, List.forall_mem_cons.2 ⟨sub7_1026, List.forall_mem_cons.2 ⟨sub7_1027, List.forall_mem_cons.2 ⟨sub7_1028, List.forall_mem_cons.2 ⟨sub7_1029, List.forall_mem_cons.2 ⟨sub7_1030, List.forall_mem_cons.2 ⟨sub7_1031, List.forall_mem_cons.2 ⟨sub7_1032, List.forall_mem_cons.2 ⟨sub7_1033, List.forall_mem_cons.2 ⟨sub7_1034, List.forall_mem_cons.2 ⟨sub7_1035, List.forall_mem_cons.2 ⟨sub7_1036, List.forall_mem_cons.2 ⟨sub7_1037, List.forall_mem_cons.2 ⟨sub7_1038, List.forall_mem_cons.2 ⟨sub7_1039, List.forall_mem_cons.2 ⟨sub7_1040, List.forall_mem_cons.2 ⟨sub7_1041, List.forall_mem_cons.2 ⟨sub7_1042, List.forall_mem_cons.2 ⟨sub7_1043, List.forall_mem_cons.2 ⟨sub7_1044, List.forall_mem_cons.2 ⟨sub7_1045, List.forall_mem_cons.2 ⟨sub7_1046, List.forall_mem_cons.2 ⟨sub7_1047, List.forall_mem_cons.2 ⟨sub7_1048, List.forall_mem_cons.2 ⟨sub7_1049, List.forall_mem_cons.2 ⟨sub7_1050, List.forall_mem_cons.2 ⟨sub7_1051, List.forall_mem_cons.2 ⟨sub7_1052, List.forall_mem_cons.2 ⟨sub7_1053, List.forall_mem_cons.2 ⟨sub7_1054, List.forall_mem_cons.2 ⟨sub7_1055, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_1056 : sub7 [6, -1] = true := by decide +kernel
theorem sub7_1057 : sub7 [6, 0] = true := by decide +kernel
theorem sub7_1058 : sub7 [6, 1] = true := by decide +kernel
theorem sub7_1059 : sub7 [6, 2] = true := by decide +kernel
theorem sub7_1060 : sub7 [6, 3] = true := by decide +kernel
theorem sb7_33 : ∀ q ∈ blk7_33, sub7 q = true := by
  unfold blk7_33
  exact List.forall_mem_cons.2 ⟨sub7_1056, List.forall_mem_cons.2 ⟨sub7_1057, List.forall_mem_cons.2 ⟨sub7_1058, List.forall_mem_cons.2 ⟨sub7_1059, List.forall_mem_cons.2 ⟨sub7_1060, List.forall_mem_nil _⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C086
