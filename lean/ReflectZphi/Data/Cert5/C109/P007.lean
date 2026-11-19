import ReflectZphi.Data.Cert5.C109.Base

namespace ReflectZphi.Data.Cert5.C109

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd6_5 : ldCheck G d6_5.U d6_5.ms ldd6_5 = true := by decide +kernel
theorem pre_okd6_5 : subPre G cell6 d6_5 = true := by decide +kernel
theorem subd6_5_0 : subd6_5 [-2] = true := by decide +kernel
theorem subd6_5_1 : subd6_5 [-1] = true := by decide +kernel
theorem subd6_5_2 : subd6_5 [0] = true := by decide +kernel
theorem subd6_5_3 : subd6_5 [1] = true := by decide +kernel
theorem subd6_5_4 : subd6_5 [2] = true := by decide +kernel
theorem sbd6_5_0 : ∀ q ∈ blkd6_5_0, subd6_5 q = true := by
  unfold blkd6_5_0
  exact List.forall_mem_cons.2 ⟨subd6_5_0, List.forall_mem_cons.2 ⟨subd6_5_1, List.forall_mem_cons.2 ⟨subd6_5_2, List.forall_mem_cons.2 ⟨subd6_5_3, List.forall_mem_cons.2 ⟨subd6_5_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd6_6 : ldCheck G d6_6.U d6_6.ms ldd6_6 = true := by decide +kernel
theorem pre_okd6_6 : subPre G cell6 d6_6 = true := by decide +kernel
theorem subd6_6_0 : subd6_6 [-1] = true := by decide +kernel
theorem subd6_6_1 : subd6_6 [0] = true := by decide +kernel
theorem subd6_6_2 : subd6_6 [1] = true := by decide +kernel
theorem sbd6_6_0 : ∀ q ∈ blkd6_6_0, subd6_6 q = true := by
  unfold blkd6_6_0
  exact List.forall_mem_cons.2 ⟨subd6_6_0, List.forall_mem_cons.2 ⟨subd6_6_1, List.forall_mem_cons.2 ⟨subd6_6_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd6_7 : ldCheck G d6_7.U d6_7.ms ldd6_7 = true := by decide +kernel
theorem pre_okd6_7 : subPre G cell6 d6_7 = true := by decide +kernel
theorem subd6_7_0 : subd6_7 [-1] = true := by decide +kernel
theorem subd6_7_1 : subd6_7 [0] = true := by decide +kernel
theorem subd6_7_2 : subd6_7 [1] = true := by decide +kernel
theorem sbd6_7_0 : ∀ q ∈ blkd6_7_0, subd6_7 q = true := by
  unfold blkd6_7_0
  exact List.forall_mem_cons.2 ⟨subd6_7_0, List.forall_mem_cons.2 ⟨subd6_7_1, List.forall_mem_cons.2 ⟨subd6_7_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd7_0 : ldCheck G d7_0.U d7_0.ms ldd7_0 = true := by decide +kernel
theorem pre_okd7_0 : subPre G cell7 d7_0 = true := by decide +kernel
theorem subd7_0_0 : subd7_0 [] = true := by decide +kernel
theorem sbd7_0_0 : ∀ q ∈ blkd7_0_0, subd7_0 q = true := by
  unfold blkd7_0_0
  exact List.forall_mem_cons.2 ⟨subd7_0_0, List.forall_mem_nil _⟩
theorem ld_okd7_1 : ldCheck G d7_1.U d7_1.ms ldd7_1 = true := by decide +kernel
theorem pre_okd7_1 : subPre G cell7 d7_1 = true := by decide +kernel
theorem subd7_1_0 : subd7_1 [-2] = true := by decide +kernel
theorem subd7_1_1 : subd7_1 [-1] = true := by decide +kernel
theorem subd7_1_2 : subd7_1 [0] = true := by decide +kernel
theorem subd7_1_3 : subd7_1 [1] = true := by decide +kernel
theorem subd7_1_4 : subd7_1 [2] = true := by decide +kernel
theorem sbd7_1_0 : ∀ q ∈ blkd7_1_0, subd7_1 q = true := by
  unfold blkd7_1_0
  exact List.forall_mem_cons.2 ⟨subd7_1_0, List.forall_mem_cons.2 ⟨subd7_1_1, List.forall_mem_cons.2 ⟨subd7_1_2, List.forall_mem_cons.2 ⟨subd7_1_3, List.forall_mem_cons.2 ⟨subd7_1_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd7_2 : ldCheck G d7_2.U d7_2.ms ldd7_2 = true := by decide +kernel
theorem pre_okd7_2 : subPre G cell7 d7_2 = true := by decide +kernel
theorem subd7_2_0 : subd7_2 [-1] = true := by decide +kernel
theorem subd7_2_1 : subd7_2 [0] = true := by decide +kernel
theorem subd7_2_2 : subd7_2 [1] = true := by decide +kernel
theorem sbd7_2_0 : ∀ q ∈ blkd7_2_0, subd7_2 q = true := by
  unfold blkd7_2_0
  exact List.forall_mem_cons.2 ⟨subd7_2_0, List.forall_mem_cons.2 ⟨subd7_2_1, List.forall_mem_cons.2 ⟨subd7_2_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd7_3 : ldCheck G d7_3.U d7_3.ms ldd7_3 = true := by decide +kernel
theorem pre_okd7_3 : subPre G cell7 d7_3 = true := by decide +kernel
theorem subd7_3_0 : subd7_3 [-2] = true := by decide +kernel
theorem subd7_3_1 : subd7_3 [-1] = true := by decide +kernel
theorem subd7_3_2 : subd7_3 [0] = true := by decide +kernel
theorem subd7_3_3 : subd7_3 [1] = true := by decide +kernel
theorem subd7_3_4 : subd7_3 [2] = true := by decide +kernel
theorem sbd7_3_0 : ∀ q ∈ blkd7_3_0, subd7_3 q = true := by
  unfold blkd7_3_0
  exact List.forall_mem_cons.2 ⟨subd7_3_0, List.forall_mem_cons.2 ⟨subd7_3_1, List.forall_mem_cons.2 ⟨subd7_3_2, List.forall_mem_cons.2 ⟨subd7_3_3, List.forall_mem_cons.2 ⟨subd7_3_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd7_4 : ldCheck G d7_4.U d7_4.ms ldd7_4 = true := by decide +kernel
theorem pre_okd7_4 : subPre G cell7 d7_4 = true := by decide +kernel
theorem subd7_4_0 : subd7_4 [-1] = true := by decide +kernel
theorem subd7_4_1 : subd7_4 [0] = true := by decide +kernel
theorem subd7_4_2 : subd7_4 [1] = true := by decide +kernel
theorem sbd7_4_0 : ∀ q ∈ blkd7_4_0, subd7_4 q = true := by
  unfold blkd7_4_0
  exact List.forall_mem_cons.2 ⟨subd7_4_0, List.forall_mem_cons.2 ⟨subd7_4_1, List.forall_mem_cons.2 ⟨subd7_4_2, List.forall_mem_nil _⟩⟩⟩

end ReflectZphi.Data.Cert5.C109
