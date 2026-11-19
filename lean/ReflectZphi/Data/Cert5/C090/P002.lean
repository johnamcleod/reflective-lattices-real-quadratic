import ReflectZphi.Data.Cert5.C090.Base

namespace ReflectZphi.Data.Cert5.C090

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd2_1 : ldCheck G d2_1.U d2_1.ms ldd2_1 = true := by decide +kernel
theorem pre_okd2_1 : subPre G cell2 d2_1 = true := by decide +kernel
theorem subd2_1_0 : subd2_1 [] = true := by decide +kernel
theorem sbd2_1_0 : ∀ q ∈ blkd2_1_0, subd2_1 q = true := by
  unfold blkd2_1_0
  exact List.forall_mem_cons.2 ⟨subd2_1_0, List.forall_mem_nil _⟩
theorem ld_okd2_2 : ldCheck G d2_2.U d2_2.ms ldd2_2 = true := by decide +kernel
theorem pre_okd2_2 : subPre G cell2 d2_2 = true := by decide +kernel
theorem subd2_2_0 : subd2_2 [] = true := by decide +kernel
theorem sbd2_2_0 : ∀ q ∈ blkd2_2_0, subd2_2 q = true := by
  unfold blkd2_2_0
  exact List.forall_mem_cons.2 ⟨subd2_2_0, List.forall_mem_nil _⟩
theorem ld_okd2_3 : ldCheck G d2_3.U d2_3.ms ldd2_3 = true := by decide +kernel
theorem pre_okd2_3 : subPre G cell2 d2_3 = true := by decide +kernel
theorem subd2_3_0 : subd2_3 [] = true := by decide +kernel
theorem sbd2_3_0 : ∀ q ∈ blkd2_3_0, subd2_3 q = true := by
  unfold blkd2_3_0
  exact List.forall_mem_cons.2 ⟨subd2_3_0, List.forall_mem_nil _⟩
theorem ld_okd2_4 : ldCheck G d2_4.U d2_4.ms ldd2_4 = true := by decide +kernel
theorem pre_okd2_4 : subPre G cell2 d2_4 = true := by decide +kernel
theorem subd2_4_0 : subd2_4 [-2] = true := by decide +kernel
theorem subd2_4_1 : subd2_4 [-1, -2] = true := by decide +kernel
theorem subd2_4_2 : subd2_4 [-1, -1] = true := by decide +kernel
theorem subd2_4_3 : subd2_4 [-1, 0] = true := by decide +kernel
theorem subd2_4_4 : subd2_4 [-1, 1] = true := by decide +kernel
theorem subd2_4_5 : subd2_4 [-1, 2] = true := by decide +kernel
theorem subd2_4_6 : subd2_4 [0, -3] = true := by decide +kernel
theorem subd2_4_7 : subd2_4 [0, -2] = true := by decide +kernel
theorem subd2_4_8 : subd2_4 [0, -1] = true := by decide +kernel
theorem subd2_4_9 : subd2_4 [0, 0] = true := by decide +kernel
theorem subd2_4_10 : subd2_4 [0, 1] = true := by decide +kernel
theorem subd2_4_11 : subd2_4 [0, 2] = true := by decide +kernel
theorem subd2_4_12 : subd2_4 [1, -3] = true := by decide +kernel
theorem subd2_4_13 : subd2_4 [1, -2] = true := by decide +kernel
theorem subd2_4_14 : subd2_4 [1, -1] = true := by decide +kernel
theorem subd2_4_15 : subd2_4 [1, 0] = true := by decide +kernel
theorem subd2_4_16 : subd2_4 [1, 1] = true := by decide +kernel
theorem subd2_4_17 : subd2_4 [2] = true := by decide +kernel
theorem sbd2_4_0 : ∀ q ∈ blkd2_4_0, subd2_4 q = true := by
  unfold blkd2_4_0
  exact List.forall_mem_cons.2 ⟨subd2_4_0, List.forall_mem_cons.2 ⟨subd2_4_1, List.forall_mem_cons.2 ⟨subd2_4_2, List.forall_mem_cons.2 ⟨subd2_4_3, List.forall_mem_cons.2 ⟨subd2_4_4, List.forall_mem_cons.2 ⟨subd2_4_5, List.forall_mem_cons.2 ⟨subd2_4_6, List.forall_mem_cons.2 ⟨subd2_4_7, List.forall_mem_cons.2 ⟨subd2_4_8, List.forall_mem_cons.2 ⟨subd2_4_9, List.forall_mem_cons.2 ⟨subd2_4_10, List.forall_mem_cons.2 ⟨subd2_4_11, List.forall_mem_cons.2 ⟨subd2_4_12, List.forall_mem_cons.2 ⟨subd2_4_13, List.forall_mem_cons.2 ⟨subd2_4_14, List.forall_mem_cons.2 ⟨subd2_4_15, List.forall_mem_cons.2 ⟨subd2_4_16, List.forall_mem_cons.2 ⟨subd2_4_17, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd2_5 : ldCheck G d2_5.U d2_5.ms ldd2_5 = true := by decide +kernel
theorem pre_okd2_5 : subPre G cell2 d2_5 = true := by decide +kernel
theorem subd2_5_0 : subd2_5 [-1, -2] = true := by decide +kernel
theorem subd2_5_1 : subd2_5 [-1, -1] = true := by decide +kernel
theorem subd2_5_2 : subd2_5 [-1, 0] = true := by decide +kernel
theorem subd2_5_3 : subd2_5 [-1, 1] = true := by decide +kernel
theorem subd2_5_4 : subd2_5 [0, -2] = true := by decide +kernel
theorem subd2_5_5 : subd2_5 [0, -1] = true := by decide +kernel
theorem subd2_5_6 : subd2_5 [0, 0, -7] = true := by decide +kernel
theorem subd2_5_7 : subd2_5 [0, 0, -6] = true := by decide +kernel
theorem subd2_5_8 : subd2_5 [0, 0, -5] = true := by decide +kernel
theorem subd2_5_9 : subd2_5 [0, 0, -4] = true := by decide +kernel
theorem subd2_5_10 : subd2_5 [0, 0, -3] = true := by decide +kernel
theorem subd2_5_11 : subd2_5 [0, 0, -2] = true := by decide +kernel
theorem subd2_5_12 : subd2_5 [0, 0, -1] = true := by decide +kernel
theorem subd2_5_13 : subd2_5 [0, 0, 0] = true := by decide +kernel
theorem subd2_5_14 : subd2_5 [0, 0, 1] = true := by decide +kernel
theorem subd2_5_15 : subd2_5 [0, 0, 2] = true := by decide +kernel
theorem subd2_5_16 : subd2_5 [0, 0, 3] = true := by decide +kernel
theorem subd2_5_17 : subd2_5 [0, 0, 4] = true := by decide +kernel
theorem subd2_5_18 : subd2_5 [0, 0, 5] = true := by decide +kernel
theorem subd2_5_19 : subd2_5 [0, 0, 6] = true := by decide +kernel
theorem subd2_5_20 : subd2_5 [0, 1] = true := by decide +kernel
theorem subd2_5_21 : subd2_5 [1, -2] = true := by decide +kernel
theorem subd2_5_22 : subd2_5 [1, -1] = true := by decide +kernel
theorem subd2_5_23 : subd2_5 [1, 0] = true := by decide +kernel
theorem subd2_5_24 : subd2_5 [1, 1] = true := by decide +kernel
theorem sbd2_5_0 : ∀ q ∈ blkd2_5_0, subd2_5 q = true := by
  unfold blkd2_5_0
  exact List.forall_mem_cons.2 ⟨subd2_5_0, List.forall_mem_cons.2 ⟨subd2_5_1, List.forall_mem_cons.2 ⟨subd2_5_2, List.forall_mem_cons.2 ⟨subd2_5_3, List.forall_mem_cons.2 ⟨subd2_5_4, List.forall_mem_cons.2 ⟨subd2_5_5, List.forall_mem_cons.2 ⟨subd2_5_6, List.forall_mem_cons.2 ⟨subd2_5_7, List.forall_mem_cons.2 ⟨subd2_5_8, List.forall_mem_cons.2 ⟨subd2_5_9, List.forall_mem_cons.2 ⟨subd2_5_10, List.forall_mem_cons.2 ⟨subd2_5_11, List.forall_mem_cons.2 ⟨subd2_5_12, List.forall_mem_cons.2 ⟨subd2_5_13, List.forall_mem_cons.2 ⟨subd2_5_14, List.forall_mem_cons.2 ⟨subd2_5_15, List.forall_mem_cons.2 ⟨subd2_5_16, List.forall_mem_cons.2 ⟨subd2_5_17, List.forall_mem_cons.2 ⟨subd2_5_18, List.forall_mem_cons.2 ⟨subd2_5_19, List.forall_mem_cons.2 ⟨subd2_5_20, List.forall_mem_cons.2 ⟨subd2_5_21, List.forall_mem_cons.2 ⟨subd2_5_22, List.forall_mem_cons.2 ⟨subd2_5_23, List.forall_mem_cons.2 ⟨subd2_5_24, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd2_6 : ldCheck G d2_6.U d2_6.ms ldd2_6 = true := by decide +kernel
theorem pre_okd2_6 : subPre G cell2 d2_6 = true := by decide +kernel
theorem subd2_6_0 : subd2_6 [] = true := by decide +kernel
theorem sbd2_6_0 : ∀ q ∈ blkd2_6_0, subd2_6 q = true := by
  unfold blkd2_6_0
  exact List.forall_mem_cons.2 ⟨subd2_6_0, List.forall_mem_nil _⟩
theorem ld_okd2_7 : ldCheck G d2_7.U d2_7.ms ldd2_7 = true := by decide +kernel
theorem pre_okd2_7 : subPre G cell2 d2_7 = true := by decide +kernel
theorem subd2_7_0 : subd2_7 [-2] = true := by decide +kernel
theorem subd2_7_1 : subd2_7 [-1] = true := by decide +kernel
theorem subd2_7_2 : subd2_7 [0] = true := by decide +kernel
theorem subd2_7_3 : subd2_7 [1] = true := by decide +kernel
theorem subd2_7_4 : subd2_7 [2] = true := by decide +kernel
theorem sbd2_7_0 : ∀ q ∈ blkd2_7_0, subd2_7 q = true := by
  unfold blkd2_7_0
  exact List.forall_mem_cons.2 ⟨subd2_7_0, List.forall_mem_cons.2 ⟨subd2_7_1, List.forall_mem_cons.2 ⟨subd2_7_2, List.forall_mem_cons.2 ⟨subd2_7_3, List.forall_mem_cons.2 ⟨subd2_7_4, List.forall_mem_nil _⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C090
