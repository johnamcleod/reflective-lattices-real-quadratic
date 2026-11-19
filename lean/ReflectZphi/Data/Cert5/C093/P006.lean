import ReflectZphi.Data.Cert5.C093.Base

namespace ReflectZphi.Data.Cert5.C093

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd5_0_992 : subd5_0 [4, -1, 1] = true := by decide +kernel
theorem subd5_0_993 : subd5_0 [4, -1, 2] = true := by decide +kernel
theorem subd5_0_994 : subd5_0 [4, -1, 3] = true := by decide +kernel
theorem subd5_0_995 : subd5_0 [4, -1, 4] = true := by decide +kernel
theorem subd5_0_996 : subd5_0 [4, -1, 5] = true := by decide +kernel
theorem subd5_0_997 : subd5_0 [4, -1, 6] = true := by decide +kernel
theorem subd5_0_998 : subd5_0 [4, -1, 7] = true := by decide +kernel
theorem subd5_0_999 : subd5_0 [4, -1, 8] = true := by decide +kernel
theorem subd5_0_1000 : subd5_0 [4, 0, -5] = true := by decide +kernel
theorem subd5_0_1001 : subd5_0 [4, 0, -4] = true := by decide +kernel
theorem subd5_0_1002 : subd5_0 [4, 0, -3] = true := by decide +kernel
theorem subd5_0_1003 : subd5_0 [4, 0, -2] = true := by decide +kernel
theorem subd5_0_1004 : subd5_0 [4, 0, -1] = true := by decide +kernel
theorem subd5_0_1005 : subd5_0 [4, 0, 0] = true := by decide +kernel
theorem subd5_0_1006 : subd5_0 [4, 0, 1] = true := by decide +kernel
theorem subd5_0_1007 : subd5_0 [4, 0, 2] = true := by decide +kernel
theorem subd5_0_1008 : subd5_0 [4, 0, 3] = true := by decide +kernel
theorem subd5_0_1009 : subd5_0 [4, 0, 4] = true := by decide +kernel
theorem subd5_0_1010 : subd5_0 [4, 0, 5] = true := by decide +kernel
theorem subd5_0_1011 : subd5_0 [4, 0, 6] = true := by decide +kernel
theorem subd5_0_1012 : subd5_0 [4, 0, 7] = true := by decide +kernel
theorem subd5_0_1013 : subd5_0 [4, 1] = true := by decide +kernel
theorem subd5_0_1014 : subd5_0 [4, 2] = true := by decide +kernel
theorem subd5_0_1015 : subd5_0 [4, 3] = true := by decide +kernel
theorem subd5_0_1016 : subd5_0 [5, -3] = true := by decide +kernel
theorem subd5_0_1017 : subd5_0 [5, -2] = true := by decide +kernel
theorem subd5_0_1018 : subd5_0 [5, -1] = true := by decide +kernel
theorem subd5_0_1019 : subd5_0 [5, 0] = true := by decide +kernel
theorem subd5_0_1020 : subd5_0 [5, 1] = true := by decide +kernel
theorem sbd5_0_31 : ∀ q ∈ blkd5_0_31, subd5_0 q = true := by
  unfold blkd5_0_31
  exact List.forall_mem_cons.2 ⟨subd5_0_992, List.forall_mem_cons.2 ⟨subd5_0_993, List.forall_mem_cons.2 ⟨subd5_0_994, List.forall_mem_cons.2 ⟨subd5_0_995, List.forall_mem_cons.2 ⟨subd5_0_996, List.forall_mem_cons.2 ⟨subd5_0_997, List.forall_mem_cons.2 ⟨subd5_0_998, List.forall_mem_cons.2 ⟨subd5_0_999, List.forall_mem_cons.2 ⟨subd5_0_1000, List.forall_mem_cons.2 ⟨subd5_0_1001, List.forall_mem_cons.2 ⟨subd5_0_1002, List.forall_mem_cons.2 ⟨subd5_0_1003, List.forall_mem_cons.2 ⟨subd5_0_1004, List.forall_mem_cons.2 ⟨subd5_0_1005, List.forall_mem_cons.2 ⟨subd5_0_1006, List.forall_mem_cons.2 ⟨subd5_0_1007, List.forall_mem_cons.2 ⟨subd5_0_1008, List.forall_mem_cons.2 ⟨subd5_0_1009, List.forall_mem_cons.2 ⟨subd5_0_1010, List.forall_mem_cons.2 ⟨subd5_0_1011, List.forall_mem_cons.2 ⟨subd5_0_1012, List.forall_mem_cons.2 ⟨subd5_0_1013, List.forall_mem_cons.2 ⟨subd5_0_1014, List.forall_mem_cons.2 ⟨subd5_0_1015, List.forall_mem_cons.2 ⟨subd5_0_1016, List.forall_mem_cons.2 ⟨subd5_0_1017, List.forall_mem_cons.2 ⟨subd5_0_1018, List.forall_mem_cons.2 ⟨subd5_0_1019, List.forall_mem_cons.2 ⟨subd5_0_1020, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_1 : ldCheck G d5_1.U d5_1.ms ldd5_1 = true := by decide +kernel
theorem pre_okd5_1 : subPre G cell5 d5_1 = true := by decide +kernel
theorem subd5_1_0 : subd5_1 [-2] = true := by decide +kernel
theorem subd5_1_1 : subd5_1 [-1] = true := by decide +kernel
theorem subd5_1_2 : subd5_1 [0] = true := by decide +kernel
theorem subd5_1_3 : subd5_1 [1] = true := by decide +kernel
theorem subd5_1_4 : subd5_1 [2] = true := by decide +kernel
theorem sbd5_1_0 : ∀ q ∈ blkd5_1_0, subd5_1 q = true := by
  unfold blkd5_1_0
  exact List.forall_mem_cons.2 ⟨subd5_1_0, List.forall_mem_cons.2 ⟨subd5_1_1, List.forall_mem_cons.2 ⟨subd5_1_2, List.forall_mem_cons.2 ⟨subd5_1_3, List.forall_mem_cons.2 ⟨subd5_1_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd5_2 : ldCheck G d5_2.U d5_2.ms ldd5_2 = true := by decide +kernel
theorem pre_okd5_2 : subPre G cell5 d5_2 = true := by decide +kernel
theorem subd5_2_0 : subd5_2 [] = true := by decide +kernel
theorem sbd5_2_0 : ∀ q ∈ blkd5_2_0, subd5_2 q = true := by
  unfold blkd5_2_0
  exact List.forall_mem_cons.2 ⟨subd5_2_0, List.forall_mem_nil _⟩
theorem ld_okd5_3 : ldCheck G d5_3.U d5_3.ms ldd5_3 = true := by decide +kernel
theorem pre_okd5_3 : subPre G cell5 d5_3 = true := by decide +kernel
theorem subd5_3_0 : subd5_3 [-1] = true := by decide +kernel
theorem subd5_3_1 : subd5_3 [0] = true := by decide +kernel
theorem subd5_3_2 : subd5_3 [1] = true := by decide +kernel
theorem sbd5_3_0 : ∀ q ∈ blkd5_3_0, subd5_3 q = true := by
  unfold blkd5_3_0
  exact List.forall_mem_cons.2 ⟨subd5_3_0, List.forall_mem_cons.2 ⟨subd5_3_1, List.forall_mem_cons.2 ⟨subd5_3_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd5_4 : ldCheck G d5_4.U d5_4.ms ldd5_4 = true := by decide +kernel
theorem pre_okd5_4 : subPre G cell5 d5_4 = true := by decide +kernel
theorem subd5_4_0 : subd5_4 [-2] = true := by decide +kernel
theorem subd5_4_1 : subd5_4 [-1] = true := by decide +kernel
theorem subd5_4_2 : subd5_4 [0] = true := by decide +kernel
theorem subd5_4_3 : subd5_4 [1] = true := by decide +kernel
theorem subd5_4_4 : subd5_4 [2] = true := by decide +kernel
theorem sbd5_4_0 : ∀ q ∈ blkd5_4_0, subd5_4 q = true := by
  unfold blkd5_4_0
  exact List.forall_mem_cons.2 ⟨subd5_4_0, List.forall_mem_cons.2 ⟨subd5_4_1, List.forall_mem_cons.2 ⟨subd5_4_2, List.forall_mem_cons.2 ⟨subd5_4_3, List.forall_mem_cons.2 ⟨subd5_4_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd6_0 : ldCheck G d6_0.U d6_0.ms ldd6_0 = true := by decide +kernel
theorem pre_okd6_0 : subPre G cell6 d6_0 = true := by decide +kernel
theorem subd6_0_0 : subd6_0 [-7, -3] = true := by decide +kernel
theorem subd6_0_1 : subd6_0 [-7, -2] = true := by decide +kernel
theorem subd6_0_2 : subd6_0 [-7, -1] = true := by decide +kernel
theorem subd6_0_3 : subd6_0 [-7, 0] = true := by decide +kernel
theorem subd6_0_4 : subd6_0 [-7, 1] = true := by decide +kernel
theorem subd6_0_5 : subd6_0 [-7, 2] = true := by decide +kernel
theorem subd6_0_6 : subd6_0 [-7, 3] = true := by decide +kernel
theorem subd6_0_7 : subd6_0 [-7, 4] = true := by decide +kernel
theorem subd6_0_8 : subd6_0 [-6, -5] = true := by decide +kernel
theorem subd6_0_9 : subd6_0 [-6, -4] = true := by decide +kernel
theorem subd6_0_10 : subd6_0 [-6, -3] = true := by decide +kernel
theorem subd6_0_11 : subd6_0 [-6, -2] = true := by decide +kernel
theorem subd6_0_12 : subd6_0 [-6, -1] = true := by decide +kernel
theorem subd6_0_13 : subd6_0 [-6, 0] = true := by decide +kernel
theorem subd6_0_14 : subd6_0 [-6, 1] = true := by decide +kernel
theorem subd6_0_15 : subd6_0 [-6, 2] = true := by decide +kernel
theorem subd6_0_16 : subd6_0 [-6, 3] = true := by decide +kernel
theorem subd6_0_17 : subd6_0 [-6, 4] = true := by decide +kernel
theorem subd6_0_18 : subd6_0 [-6, 5] = true := by decide +kernel
theorem subd6_0_19 : subd6_0 [-5, -6] = true := by decide +kernel
theorem subd6_0_20 : subd6_0 [-5, -5] = true := by decide +kernel
theorem subd6_0_21 : subd6_0 [-5, -4] = true := by decide +kernel
theorem subd6_0_22 : subd6_0 [-5, -3] = true := by decide +kernel
theorem subd6_0_23 : subd6_0 [-5, -2] = true := by decide +kernel
theorem subd6_0_24 : subd6_0 [-5, -1] = true := by decide +kernel
theorem subd6_0_25 : subd6_0 [-5, 0, -7] = true := by decide +kernel
theorem subd6_0_26 : subd6_0 [-5, 0, -6] = true := by decide +kernel
theorem subd6_0_27 : subd6_0 [-5, 0, -5] = true := by decide +kernel
theorem subd6_0_28 : subd6_0 [-5, 0, -4] = true := by decide +kernel
theorem subd6_0_29 : subd6_0 [-5, 0, -3] = true := by decide +kernel
theorem subd6_0_30 : subd6_0 [-5, 0, -2] = true := by decide +kernel
theorem subd6_0_31 : subd6_0 [-5, 0, -1] = true := by decide +kernel
theorem sbd6_0_0 : ∀ q ∈ blkd6_0_0, subd6_0 q = true := by
  unfold blkd6_0_0
  exact List.forall_mem_cons.2 ⟨subd6_0_0, List.forall_mem_cons.2 ⟨subd6_0_1, List.forall_mem_cons.2 ⟨subd6_0_2, List.forall_mem_cons.2 ⟨subd6_0_3, List.forall_mem_cons.2 ⟨subd6_0_4, List.forall_mem_cons.2 ⟨subd6_0_5, List.forall_mem_cons.2 ⟨subd6_0_6, List.forall_mem_cons.2 ⟨subd6_0_7, List.forall_mem_cons.2 ⟨subd6_0_8, List.forall_mem_cons.2 ⟨subd6_0_9, List.forall_mem_cons.2 ⟨subd6_0_10, List.forall_mem_cons.2 ⟨subd6_0_11, List.forall_mem_cons.2 ⟨subd6_0_12, List.forall_mem_cons.2 ⟨subd6_0_13, List.forall_mem_cons.2 ⟨subd6_0_14, List.forall_mem_cons.2 ⟨subd6_0_15, List.forall_mem_cons.2 ⟨subd6_0_16, List.forall_mem_cons.2 ⟨subd6_0_17, List.forall_mem_cons.2 ⟨subd6_0_18, List.forall_mem_cons.2 ⟨subd6_0_19, List.forall_mem_cons.2 ⟨subd6_0_20, List.forall_mem_cons.2 ⟨subd6_0_21, List.forall_mem_cons.2 ⟨subd6_0_22, List.forall_mem_cons.2 ⟨subd6_0_23, List.forall_mem_cons.2 ⟨subd6_0_24, List.forall_mem_cons.2 ⟨subd6_0_25, List.forall_mem_cons.2 ⟨subd6_0_26, List.forall_mem_cons.2 ⟨subd6_0_27, List.forall_mem_cons.2 ⟨subd6_0_28, List.forall_mem_cons.2 ⟨subd6_0_29, List.forall_mem_cons.2 ⟨subd6_0_30, List.forall_mem_cons.2 ⟨subd6_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C093
