import ReflectZphi.Data.Cert5.C115.Base

namespace ReflectZphi.Data.Cert5.C115

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd7_8_0 : subd7_8 [-2] = true := by decide +kernel
theorem subd7_8_1 : subd7_8 [-1, -3] = true := by decide +kernel
theorem subd7_8_2 : subd7_8 [-1, -2] = true := by decide +kernel
theorem subd7_8_3 : subd7_8 [-1, -1] = true := by decide +kernel
theorem subd7_8_4 : subd7_8 [-1, 0] = true := by decide +kernel
theorem subd7_8_5 : subd7_8 [-1, 1] = true := by decide +kernel
theorem subd7_8_6 : subd7_8 [-1, 2] = true := by decide +kernel
theorem subd7_8_7 : subd7_8 [0, -3] = true := by decide +kernel
theorem subd7_8_8 : subd7_8 [0, -2] = true := by decide +kernel
theorem subd7_8_9 : subd7_8 [0, -1] = true := by decide +kernel
theorem subd7_8_10 : subd7_8 [0, 0] = true := by decide +kernel
theorem subd7_8_11 : subd7_8 [0, 1] = true := by decide +kernel
theorem subd7_8_12 : subd7_8 [0, 2] = true := by decide +kernel
theorem subd7_8_13 : subd7_8 [1, -3] = true := by decide +kernel
theorem subd7_8_14 : subd7_8 [1, -2] = true := by decide +kernel
theorem subd7_8_15 : subd7_8 [1, -1] = true := by decide +kernel
theorem subd7_8_16 : subd7_8 [1, 0] = true := by decide +kernel
theorem subd7_8_17 : subd7_8 [1, 1] = true := by decide +kernel
theorem subd7_8_18 : subd7_8 [1, 2] = true := by decide +kernel
theorem subd7_8_19 : subd7_8 [2] = true := by decide +kernel
theorem sbd7_8_0 : ∀ q ∈ blkd7_8_0, subd7_8 q = true := by
  unfold blkd7_8_0
  exact List.forall_mem_cons.2 ⟨subd7_8_0, List.forall_mem_cons.2 ⟨subd7_8_1, List.forall_mem_cons.2 ⟨subd7_8_2, List.forall_mem_cons.2 ⟨subd7_8_3, List.forall_mem_cons.2 ⟨subd7_8_4, List.forall_mem_cons.2 ⟨subd7_8_5, List.forall_mem_cons.2 ⟨subd7_8_6, List.forall_mem_cons.2 ⟨subd7_8_7, List.forall_mem_cons.2 ⟨subd7_8_8, List.forall_mem_cons.2 ⟨subd7_8_9, List.forall_mem_cons.2 ⟨subd7_8_10, List.forall_mem_cons.2 ⟨subd7_8_11, List.forall_mem_cons.2 ⟨subd7_8_12, List.forall_mem_cons.2 ⟨subd7_8_13, List.forall_mem_cons.2 ⟨subd7_8_14, List.forall_mem_cons.2 ⟨subd7_8_15, List.forall_mem_cons.2 ⟨subd7_8_16, List.forall_mem_cons.2 ⟨subd7_8_17, List.forall_mem_cons.2 ⟨subd7_8_18, List.forall_mem_cons.2 ⟨subd7_8_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_9 : ldCheck G d7_9.U d7_9.ms ldd7_9 = true := by decide +kernel
theorem pre_okd7_9 : subPre G cell7 d7_9 = true := by decide +kernel
theorem subd7_9_0 : subd7_9 [] = true := by decide +kernel
theorem sbd7_9_0 : ∀ q ∈ blkd7_9_0, subd7_9 q = true := by
  unfold blkd7_9_0
  exact List.forall_mem_cons.2 ⟨subd7_9_0, List.forall_mem_nil _⟩
theorem ld_okd7_10 : ldCheck G d7_10.U d7_10.ms ldd7_10 = true := by decide +kernel
theorem pre_okd7_10 : subPre G cell7 d7_10 = true := by decide +kernel
theorem subd7_10_0 : subd7_10 [-1] = true := by decide +kernel
theorem subd7_10_1 : subd7_10 [0, -3] = true := by decide +kernel
theorem subd7_10_2 : subd7_10 [0, -2] = true := by decide +kernel
theorem subd7_10_3 : subd7_10 [0, -1] = true := by decide +kernel
theorem subd7_10_4 : subd7_10 [0, 0] = true := by decide +kernel
theorem subd7_10_5 : subd7_10 [0, 1] = true := by decide +kernel
theorem subd7_10_6 : subd7_10 [0, 2] = true := by decide +kernel
theorem subd7_10_7 : subd7_10 [1] = true := by decide +kernel
theorem sbd7_10_0 : ∀ q ∈ blkd7_10_0, subd7_10 q = true := by
  unfold blkd7_10_0
  exact List.forall_mem_cons.2 ⟨subd7_10_0, List.forall_mem_cons.2 ⟨subd7_10_1, List.forall_mem_cons.2 ⟨subd7_10_2, List.forall_mem_cons.2 ⟨subd7_10_3, List.forall_mem_cons.2 ⟨subd7_10_4, List.forall_mem_cons.2 ⟨subd7_10_5, List.forall_mem_cons.2 ⟨subd7_10_6, List.forall_mem_cons.2 ⟨subd7_10_7, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_11 : ldCheck G d7_11.U d7_11.ms ldd7_11 = true := by decide +kernel
theorem pre_okd7_11 : subPre G cell7 d7_11 = true := by decide +kernel
theorem subd7_11_0 : subd7_11 [] = true := by decide +kernel
theorem sbd7_11_0 : ∀ q ∈ blkd7_11_0, subd7_11 q = true := by
  unfold blkd7_11_0
  exact List.forall_mem_cons.2 ⟨subd7_11_0, List.forall_mem_nil _⟩
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
theorem ld_okd8_4 : ldCheck G d8_4.U d8_4.ms ldd8_4 = true := by decide +kernel
theorem pre_okd8_4 : subPre G cell8 d8_4 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C115
