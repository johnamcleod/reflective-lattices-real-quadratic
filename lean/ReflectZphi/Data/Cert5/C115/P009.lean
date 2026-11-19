import ReflectZphi.Data.Cert5.C115.Base

namespace ReflectZphi.Data.Cert5.C115

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_6_0 : subd6_6 [-2] = true := by decide +kernel
theorem subd6_6_1 : subd6_6 [-1, -3] = true := by decide +kernel
theorem subd6_6_2 : subd6_6 [-1, -2] = true := by decide +kernel
theorem subd6_6_3 : subd6_6 [-1, -1] = true := by decide +kernel
theorem subd6_6_4 : subd6_6 [-1, 0] = true := by decide +kernel
theorem subd6_6_5 : subd6_6 [-1, 1] = true := by decide +kernel
theorem subd6_6_6 : subd6_6 [-1, 2] = true := by decide +kernel
theorem subd6_6_7 : subd6_6 [0, -3] = true := by decide +kernel
theorem subd6_6_8 : subd6_6 [0, -2] = true := by decide +kernel
theorem subd6_6_9 : subd6_6 [0, -1] = true := by decide +kernel
theorem subd6_6_10 : subd6_6 [0, 0] = true := by decide +kernel
theorem subd6_6_11 : subd6_6 [0, 1] = true := by decide +kernel
theorem subd6_6_12 : subd6_6 [0, 2] = true := by decide +kernel
theorem subd6_6_13 : subd6_6 [1, -3] = true := by decide +kernel
theorem subd6_6_14 : subd6_6 [1, -2] = true := by decide +kernel
theorem subd6_6_15 : subd6_6 [1, -1] = true := by decide +kernel
theorem subd6_6_16 : subd6_6 [1, 0] = true := by decide +kernel
theorem subd6_6_17 : subd6_6 [1, 1] = true := by decide +kernel
theorem subd6_6_18 : subd6_6 [1, 2] = true := by decide +kernel
theorem subd6_6_19 : subd6_6 [2] = true := by decide +kernel
theorem sbd6_6_0 : ∀ q ∈ blkd6_6_0, subd6_6 q = true := by
  unfold blkd6_6_0
  exact List.forall_mem_cons.2 ⟨subd6_6_0, List.forall_mem_cons.2 ⟨subd6_6_1, List.forall_mem_cons.2 ⟨subd6_6_2, List.forall_mem_cons.2 ⟨subd6_6_3, List.forall_mem_cons.2 ⟨subd6_6_4, List.forall_mem_cons.2 ⟨subd6_6_5, List.forall_mem_cons.2 ⟨subd6_6_6, List.forall_mem_cons.2 ⟨subd6_6_7, List.forall_mem_cons.2 ⟨subd6_6_8, List.forall_mem_cons.2 ⟨subd6_6_9, List.forall_mem_cons.2 ⟨subd6_6_10, List.forall_mem_cons.2 ⟨subd6_6_11, List.forall_mem_cons.2 ⟨subd6_6_12, List.forall_mem_cons.2 ⟨subd6_6_13, List.forall_mem_cons.2 ⟨subd6_6_14, List.forall_mem_cons.2 ⟨subd6_6_15, List.forall_mem_cons.2 ⟨subd6_6_16, List.forall_mem_cons.2 ⟨subd6_6_17, List.forall_mem_cons.2 ⟨subd6_6_18, List.forall_mem_cons.2 ⟨subd6_6_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_7 : ldCheck G d6_7.U d6_7.ms ldd6_7 = true := by decide +kernel
theorem pre_okd6_7 : subPre G cell6 d6_7 = true := by decide +kernel
theorem subd6_7_0 : subd6_7 [-2] = true := by decide +kernel
theorem subd6_7_1 : subd6_7 [-1] = true := by decide +kernel
theorem subd6_7_2 : subd6_7 [0] = true := by decide +kernel
theorem subd6_7_3 : subd6_7 [1] = true := by decide +kernel
theorem subd6_7_4 : subd6_7 [2] = true := by decide +kernel
theorem sbd6_7_0 : ∀ q ∈ blkd6_7_0, subd6_7 q = true := by
  unfold blkd6_7_0
  exact List.forall_mem_cons.2 ⟨subd6_7_0, List.forall_mem_cons.2 ⟨subd6_7_1, List.forall_mem_cons.2 ⟨subd6_7_2, List.forall_mem_cons.2 ⟨subd6_7_3, List.forall_mem_cons.2 ⟨subd6_7_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd6_8 : ldCheck G d6_8.U d6_8.ms ldd6_8 = true := by decide +kernel
theorem pre_okd6_8 : subPre G cell6 d6_8 = true := by decide +kernel
theorem subd6_8_0 : subd6_8 [-2] = true := by decide +kernel
theorem subd6_8_1 : subd6_8 [-1] = true := by decide +kernel
theorem subd6_8_2 : subd6_8 [0, -3] = true := by decide +kernel
theorem subd6_8_3 : subd6_8 [0, -2] = true := by decide +kernel
theorem subd6_8_4 : subd6_8 [0, -1] = true := by decide +kernel
theorem subd6_8_5 : subd6_8 [0, 0] = true := by decide +kernel
theorem subd6_8_6 : subd6_8 [0, 1] = true := by decide +kernel
theorem subd6_8_7 : subd6_8 [0, 2] = true := by decide +kernel
theorem subd6_8_8 : subd6_8 [1] = true := by decide +kernel
theorem subd6_8_9 : subd6_8 [2] = true := by decide +kernel
theorem sbd6_8_0 : ∀ q ∈ blkd6_8_0, subd6_8 q = true := by
  unfold blkd6_8_0
  exact List.forall_mem_cons.2 ⟨subd6_8_0, List.forall_mem_cons.2 ⟨subd6_8_1, List.forall_mem_cons.2 ⟨subd6_8_2, List.forall_mem_cons.2 ⟨subd6_8_3, List.forall_mem_cons.2 ⟨subd6_8_4, List.forall_mem_cons.2 ⟨subd6_8_5, List.forall_mem_cons.2 ⟨subd6_8_6, List.forall_mem_cons.2 ⟨subd6_8_7, List.forall_mem_cons.2 ⟨subd6_8_8, List.forall_mem_cons.2 ⟨subd6_8_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_9 : ldCheck G d6_9.U d6_9.ms ldd6_9 = true := by decide +kernel
theorem pre_okd6_9 : subPre G cell6 d6_9 = true := by decide +kernel
theorem subd6_9_0 : subd6_9 [] = true := by decide +kernel
theorem sbd6_9_0 : ∀ q ∈ blkd6_9_0, subd6_9 q = true := by
  unfold blkd6_9_0
  exact List.forall_mem_cons.2 ⟨subd6_9_0, List.forall_mem_nil _⟩
theorem ld_okd6_10 : ldCheck G d6_10.U d6_10.ms ldd6_10 = true := by decide +kernel
theorem pre_okd6_10 : subPre G cell6 d6_10 = true := by decide +kernel
theorem subd6_10_0 : subd6_10 [-1] = true := by decide +kernel
theorem subd6_10_1 : subd6_10 [0] = true := by decide +kernel
theorem subd6_10_2 : subd6_10 [1] = true := by decide +kernel
theorem sbd6_10_0 : ∀ q ∈ blkd6_10_0, subd6_10 q = true := by
  unfold blkd6_10_0
  exact List.forall_mem_cons.2 ⟨subd6_10_0, List.forall_mem_cons.2 ⟨subd6_10_1, List.forall_mem_cons.2 ⟨subd6_10_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd6_11 : ldCheck G d6_11.U d6_11.ms ldd6_11 = true := by decide +kernel
theorem pre_okd6_11 : subPre G cell6 d6_11 = true := by decide +kernel
theorem subd6_11_0 : subd6_11 [] = true := by decide +kernel
theorem sbd6_11_0 : ∀ q ∈ blkd6_11_0, subd6_11 q = true := by
  unfold blkd6_11_0
  exact List.forall_mem_cons.2 ⟨subd6_11_0, List.forall_mem_nil _⟩
theorem ld_okd7_0 : ldCheck G d7_0.U d7_0.ms ldd7_0 = true := by decide +kernel
theorem pre_okd7_0 : subPre G cell7 d7_0 = true := by decide +kernel
theorem subd7_0_0 : subd7_0 [] = true := by decide +kernel
theorem sbd7_0_0 : ∀ q ∈ blkd7_0_0, subd7_0 q = true := by
  unfold blkd7_0_0
  exact List.forall_mem_cons.2 ⟨subd7_0_0, List.forall_mem_nil _⟩
theorem ld_okd7_1 : ldCheck G d7_1.U d7_1.ms ldd7_1 = true := by decide +kernel
theorem pre_okd7_1 : subPre G cell7 d7_1 = true := by decide +kernel
theorem subd7_1_0 : subd7_1 [] = true := by decide +kernel
theorem sbd7_1_0 : ∀ q ∈ blkd7_1_0, subd7_1 q = true := by
  unfold blkd7_1_0
  exact List.forall_mem_cons.2 ⟨subd7_1_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C115
