import ReflectZphi.Data.Cert5.C113.Base

namespace ReflectZphi.Data.Cert5.C113

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd6_8 : ldCheck G d6_8.U d6_8.ms ldd6_8 = true := by decide +kernel
theorem pre_okd6_8 : subPre G cell6 d6_8 = true := by decide +kernel
theorem subd6_8_0 : subd6_8 [-3] = true := by decide +kernel
theorem subd6_8_1 : subd6_8 [-2] = true := by decide +kernel
theorem subd6_8_2 : subd6_8 [-1] = true := by decide +kernel
theorem subd6_8_3 : subd6_8 [0] = true := by decide +kernel
theorem subd6_8_4 : subd6_8 [1] = true := by decide +kernel
theorem subd6_8_5 : subd6_8 [2] = true := by decide +kernel
theorem subd6_8_6 : subd6_8 [3] = true := by decide +kernel
theorem sbd6_8_0 : ∀ q ∈ blkd6_8_0, subd6_8 q = true := by
  unfold blkd6_8_0
  exact List.forall_mem_cons.2 ⟨subd6_8_0, List.forall_mem_cons.2 ⟨subd6_8_1, List.forall_mem_cons.2 ⟨subd6_8_2, List.forall_mem_cons.2 ⟨subd6_8_3, List.forall_mem_cons.2 ⟨subd6_8_4, List.forall_mem_cons.2 ⟨subd6_8_5, List.forall_mem_cons.2 ⟨subd6_8_6, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_9 : ldCheck G d6_9.U d6_9.ms ldd6_9 = true := by decide +kernel
theorem pre_okd6_9 : subPre G cell6 d6_9 = true := by decide +kernel
theorem subd6_9_0 : subd6_9 [] = true := by decide +kernel
theorem sbd6_9_0 : ∀ q ∈ blkd6_9_0, subd6_9 q = true := by
  unfold blkd6_9_0
  exact List.forall_mem_cons.2 ⟨subd6_9_0, List.forall_mem_nil _⟩
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
theorem subd7_4_0 : subd7_4 [] = true := by decide +kernel
theorem sbd7_4_0 : ∀ q ∈ blkd7_4_0, subd7_4 q = true := by
  unfold blkd7_4_0
  exact List.forall_mem_cons.2 ⟨subd7_4_0, List.forall_mem_nil _⟩
theorem ld_okd7_5 : ldCheck G d7_5.U d7_5.ms ldd7_5 = true := by decide +kernel
theorem pre_okd7_5 : subPre G cell7 d7_5 = true := by decide +kernel
theorem subd7_5_0 : subd7_5 [] = true := by decide +kernel
theorem sbd7_5_0 : ∀ q ∈ blkd7_5_0, subd7_5 q = true := by
  unfold blkd7_5_0
  exact List.forall_mem_cons.2 ⟨subd7_5_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C113
