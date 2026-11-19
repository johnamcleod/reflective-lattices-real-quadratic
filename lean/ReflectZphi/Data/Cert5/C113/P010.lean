import ReflectZphi.Data.Cert5.C113.Base

namespace ReflectZphi.Data.Cert5.C113

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd7_6 : ldCheck G d7_6.U d7_6.ms ldd7_6 = true := by decide +kernel
theorem pre_okd7_6 : subPre G cell7 d7_6 = true := by decide +kernel
theorem subd7_6_0 : subd7_6 [-2] = true := by decide +kernel
theorem subd7_6_1 : subd7_6 [-1] = true := by decide +kernel
theorem subd7_6_2 : subd7_6 [0] = true := by decide +kernel
theorem subd7_6_3 : subd7_6 [1] = true := by decide +kernel
theorem subd7_6_4 : subd7_6 [2] = true := by decide +kernel
theorem sbd7_6_0 : ∀ q ∈ blkd7_6_0, subd7_6 q = true := by
  unfold blkd7_6_0
  exact List.forall_mem_cons.2 ⟨subd7_6_0, List.forall_mem_cons.2 ⟨subd7_6_1, List.forall_mem_cons.2 ⟨subd7_6_2, List.forall_mem_cons.2 ⟨subd7_6_3, List.forall_mem_cons.2 ⟨subd7_6_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
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
theorem subd7_8_0 : subd7_8 [-2] = true := by decide +kernel
theorem subd7_8_1 : subd7_8 [-1] = true := by decide +kernel
theorem subd7_8_2 : subd7_8 [0, -3] = true := by decide +kernel
theorem subd7_8_3 : subd7_8 [0, -2] = true := by decide +kernel
theorem subd7_8_4 : subd7_8 [0, -1] = true := by decide +kernel
theorem subd7_8_5 : subd7_8 [0, 0] = true := by decide +kernel
theorem subd7_8_6 : subd7_8 [0, 1] = true := by decide +kernel
theorem subd7_8_7 : subd7_8 [0, 2] = true := by decide +kernel
theorem subd7_8_8 : subd7_8 [1] = true := by decide +kernel
theorem subd7_8_9 : subd7_8 [2] = true := by decide +kernel
theorem sbd7_8_0 : ∀ q ∈ blkd7_8_0, subd7_8 q = true := by
  unfold blkd7_8_0
  exact List.forall_mem_cons.2 ⟨subd7_8_0, List.forall_mem_cons.2 ⟨subd7_8_1, List.forall_mem_cons.2 ⟨subd7_8_2, List.forall_mem_cons.2 ⟨subd7_8_3, List.forall_mem_cons.2 ⟨subd7_8_4, List.forall_mem_cons.2 ⟨subd7_8_5, List.forall_mem_cons.2 ⟨subd7_8_6, List.forall_mem_cons.2 ⟨subd7_8_7, List.forall_mem_cons.2 ⟨subd7_8_8, List.forall_mem_cons.2 ⟨subd7_8_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_9 : ldCheck G d7_9.U d7_9.ms ldd7_9 = true := by decide +kernel
theorem pre_okd7_9 : subPre G cell7 d7_9 = true := by decide +kernel
theorem subd7_9_0 : subd7_9 [] = true := by decide +kernel
theorem sbd7_9_0 : ∀ q ∈ blkd7_9_0, subd7_9 q = true := by
  unfold blkd7_9_0
  exact List.forall_mem_cons.2 ⟨subd7_9_0, List.forall_mem_nil _⟩
theorem ld_okd8_0 : ldCheck G d8_0.U d8_0.ms ldd8_0 = true := by decide +kernel
theorem pre_okd8_0 : subPre G cell8 d8_0 = true := by decide +kernel
theorem subd8_0_0 : subd8_0 [] = true := by decide +kernel
theorem sbd8_0_0 : ∀ q ∈ blkd8_0_0, subd8_0 q = true := by
  unfold blkd8_0_0
  exact List.forall_mem_cons.2 ⟨subd8_0_0, List.forall_mem_nil _⟩
theorem ld_okd8_1 : ldCheck G d8_1.U d8_1.ms ldd8_1 = true := by decide +kernel
theorem pre_okd8_1 : subPre G cell8 d8_1 = true := by decide +kernel
theorem subd8_1_0 : subd8_1 [] = true := by decide +kernel
theorem sbd8_1_0 : ∀ q ∈ blkd8_1_0, subd8_1 q = true := by
  unfold blkd8_1_0
  exact List.forall_mem_cons.2 ⟨subd8_1_0, List.forall_mem_nil _⟩
theorem ld_okd8_2 : ldCheck G d8_2.U d8_2.ms ldd8_2 = true := by decide +kernel
theorem pre_okd8_2 : subPre G cell8 d8_2 = true := by decide +kernel
theorem subd8_2_0 : subd8_2 [] = true := by decide +kernel
theorem sbd8_2_0 : ∀ q ∈ blkd8_2_0, subd8_2 q = true := by
  unfold blkd8_2_0
  exact List.forall_mem_cons.2 ⟨subd8_2_0, List.forall_mem_nil _⟩
theorem ld_okd8_3 : ldCheck G d8_3.U d8_3.ms ldd8_3 = true := by decide +kernel
theorem pre_okd8_3 : subPre G cell8 d8_3 = true := by decide +kernel
theorem subd8_3_0 : subd8_3 [] = true := by decide +kernel
theorem sbd8_3_0 : ∀ q ∈ blkd8_3_0, subd8_3 q = true := by
  unfold blkd8_3_0
  exact List.forall_mem_cons.2 ⟨subd8_3_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C113
