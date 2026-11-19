import ReflectZphi.Data.Cert5.C115.Base

namespace ReflectZphi.Data.Cert5.C115

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd7_2 : ldCheck G d7_2.U d7_2.ms ldd7_2 = true := by decide +kernel
theorem pre_okd7_2 : subPre G cell7 d7_2 = true := by decide +kernel
theorem subd7_2_0 : subd7_2 [] = true := by decide +kernel
theorem sbd7_2_0 : ∀ q ∈ blkd7_2_0, subd7_2 q = true := by
  unfold blkd7_2_0
  exact List.forall_mem_cons.2 ⟨subd7_2_0, List.forall_mem_nil _⟩
theorem ld_okd7_3 : ldCheck G d7_3.U d7_3.ms ldd7_3 = true := by decide +kernel
theorem pre_okd7_3 : subPre G cell7 d7_3 = true := by decide +kernel
theorem subd7_3_0 : subd7_3 [] = true := by decide +kernel
theorem sbd7_3_0 : ∀ q ∈ blkd7_3_0, subd7_3 q = true := by
  unfold blkd7_3_0
  exact List.forall_mem_cons.2 ⟨subd7_3_0, List.forall_mem_nil _⟩
theorem ld_okd7_4 : ldCheck G d7_4.U d7_4.ms ldd7_4 = true := by decide +kernel
theorem pre_okd7_4 : subPre G cell7 d7_4 = true := by decide +kernel
theorem subd7_4_0 : subd7_4 [-1, -3] = true := by decide +kernel
theorem subd7_4_1 : subd7_4 [-1, -2] = true := by decide +kernel
theorem subd7_4_2 : subd7_4 [-1, -1] = true := by decide +kernel
theorem subd7_4_3 : subd7_4 [-1, 0] = true := by decide +kernel
theorem subd7_4_4 : subd7_4 [-1, 1] = true := by decide +kernel
theorem subd7_4_5 : subd7_4 [0, -3] = true := by decide +kernel
theorem subd7_4_6 : subd7_4 [0, -2] = true := by decide +kernel
theorem subd7_4_7 : subd7_4 [0, -1] = true := by decide +kernel
theorem subd7_4_8 : subd7_4 [0, 0] = true := by decide +kernel
theorem subd7_4_9 : subd7_4 [0, 1] = true := by decide +kernel
theorem subd7_4_10 : subd7_4 [0, 2] = true := by decide +kernel
theorem subd7_4_11 : subd7_4 [1, -2] = true := by decide +kernel
theorem subd7_4_12 : subd7_4 [1, -1] = true := by decide +kernel
theorem subd7_4_13 : subd7_4 [1, 0] = true := by decide +kernel
theorem subd7_4_14 : subd7_4 [1, 1] = true := by decide +kernel
theorem subd7_4_15 : subd7_4 [1, 2] = true := by decide +kernel
theorem sbd7_4_0 : ∀ q ∈ blkd7_4_0, subd7_4 q = true := by
  unfold blkd7_4_0
  exact List.forall_mem_cons.2 ⟨subd7_4_0, List.forall_mem_cons.2 ⟨subd7_4_1, List.forall_mem_cons.2 ⟨subd7_4_2, List.forall_mem_cons.2 ⟨subd7_4_3, List.forall_mem_cons.2 ⟨subd7_4_4, List.forall_mem_cons.2 ⟨subd7_4_5, List.forall_mem_cons.2 ⟨subd7_4_6, List.forall_mem_cons.2 ⟨subd7_4_7, List.forall_mem_cons.2 ⟨subd7_4_8, List.forall_mem_cons.2 ⟨subd7_4_9, List.forall_mem_cons.2 ⟨subd7_4_10, List.forall_mem_cons.2 ⟨subd7_4_11, List.forall_mem_cons.2 ⟨subd7_4_12, List.forall_mem_cons.2 ⟨subd7_4_13, List.forall_mem_cons.2 ⟨subd7_4_14, List.forall_mem_cons.2 ⟨subd7_4_15, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_5 : ldCheck G d7_5.U d7_5.ms ldd7_5 = true := by decide +kernel
theorem pre_okd7_5 : subPre G cell7 d7_5 = true := by decide +kernel
theorem subd7_5_0 : subd7_5 [-1] = true := by decide +kernel
theorem subd7_5_1 : subd7_5 [0] = true := by decide +kernel
theorem subd7_5_2 : subd7_5 [1] = true := by decide +kernel
theorem sbd7_5_0 : ∀ q ∈ blkd7_5_0, subd7_5 q = true := by
  unfold blkd7_5_0
  exact List.forall_mem_cons.2 ⟨subd7_5_0, List.forall_mem_cons.2 ⟨subd7_5_1, List.forall_mem_cons.2 ⟨subd7_5_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd7_6 : ldCheck G d7_6.U d7_6.ms ldd7_6 = true := by decide +kernel
theorem pre_okd7_6 : subPre G cell7 d7_6 = true := by decide +kernel
theorem subd7_6_0 : subd7_6 [-2] = true := by decide +kernel
theorem subd7_6_1 : subd7_6 [-1, -3] = true := by decide +kernel
theorem subd7_6_2 : subd7_6 [-1, -2] = true := by decide +kernel
theorem subd7_6_3 : subd7_6 [-1, -1] = true := by decide +kernel
theorem subd7_6_4 : subd7_6 [-1, 0] = true := by decide +kernel
theorem subd7_6_5 : subd7_6 [-1, 1] = true := by decide +kernel
theorem subd7_6_6 : subd7_6 [-1, 2] = true := by decide +kernel
theorem subd7_6_7 : subd7_6 [0, -3] = true := by decide +kernel
theorem subd7_6_8 : subd7_6 [0, -2] = true := by decide +kernel
theorem subd7_6_9 : subd7_6 [0, -1] = true := by decide +kernel
theorem subd7_6_10 : subd7_6 [0, 0] = true := by decide +kernel
theorem subd7_6_11 : subd7_6 [0, 1] = true := by decide +kernel
theorem subd7_6_12 : subd7_6 [0, 2] = true := by decide +kernel
theorem subd7_6_13 : subd7_6 [1, -3] = true := by decide +kernel
theorem subd7_6_14 : subd7_6 [1, -2] = true := by decide +kernel
theorem subd7_6_15 : subd7_6 [1, -1] = true := by decide +kernel
theorem subd7_6_16 : subd7_6 [1, 0] = true := by decide +kernel
theorem subd7_6_17 : subd7_6 [1, 1] = true := by decide +kernel
theorem subd7_6_18 : subd7_6 [1, 2] = true := by decide +kernel
theorem subd7_6_19 : subd7_6 [2] = true := by decide +kernel
theorem sbd7_6_0 : ∀ q ∈ blkd7_6_0, subd7_6 q = true := by
  unfold blkd7_6_0
  exact List.forall_mem_cons.2 ⟨subd7_6_0, List.forall_mem_cons.2 ⟨subd7_6_1, List.forall_mem_cons.2 ⟨subd7_6_2, List.forall_mem_cons.2 ⟨subd7_6_3, List.forall_mem_cons.2 ⟨subd7_6_4, List.forall_mem_cons.2 ⟨subd7_6_5, List.forall_mem_cons.2 ⟨subd7_6_6, List.forall_mem_cons.2 ⟨subd7_6_7, List.forall_mem_cons.2 ⟨subd7_6_8, List.forall_mem_cons.2 ⟨subd7_6_9, List.forall_mem_cons.2 ⟨subd7_6_10, List.forall_mem_cons.2 ⟨subd7_6_11, List.forall_mem_cons.2 ⟨subd7_6_12, List.forall_mem_cons.2 ⟨subd7_6_13, List.forall_mem_cons.2 ⟨subd7_6_14, List.forall_mem_cons.2 ⟨subd7_6_15, List.forall_mem_cons.2 ⟨subd7_6_16, List.forall_mem_cons.2 ⟨subd7_6_17, List.forall_mem_cons.2 ⟨subd7_6_18, List.forall_mem_cons.2 ⟨subd7_6_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_7 : ldCheck G d7_7.U d7_7.ms ldd7_7 = true := by decide +kernel
theorem pre_okd7_7 : subPre G cell7 d7_7 = true := by decide +kernel
theorem subd7_7_0 : subd7_7 [-2] = true := by decide +kernel
theorem subd7_7_1 : subd7_7 [-1] = true := by decide +kernel
theorem subd7_7_2 : subd7_7 [0] = true := by decide +kernel
theorem subd7_7_3 : subd7_7 [1] = true := by decide +kernel
theorem subd7_7_4 : subd7_7 [2] = true := by decide +kernel
theorem sbd7_7_0 : ∀ q ∈ blkd7_7_0, subd7_7 q = true := by
  unfold blkd7_7_0
  exact List.forall_mem_cons.2 ⟨subd7_7_0, List.forall_mem_cons.2 ⟨subd7_7_1, List.forall_mem_cons.2 ⟨subd7_7_2, List.forall_mem_cons.2 ⟨subd7_7_3, List.forall_mem_cons.2 ⟨subd7_7_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd7_8 : ldCheck G d7_8.U d7_8.ms ldd7_8 = true := by decide +kernel
theorem pre_okd7_8 : subPre G cell7 d7_8 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C115
