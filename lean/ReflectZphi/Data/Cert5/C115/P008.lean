import ReflectZphi.Data.Cert5.C115.Base

namespace ReflectZphi.Data.Cert5.C115

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd5_11 : ldCheck G d5_11.U d5_11.ms ldd5_11 = true := by decide +kernel
theorem pre_okd5_11 : subPre G cell5 d5_11 = true := by decide +kernel
theorem subd5_11_0 : subd5_11 [] = true := by decide +kernel
theorem sbd5_11_0 : ∀ q ∈ blkd5_11_0, subd5_11 q = true := by
  unfold blkd5_11_0
  exact List.forall_mem_cons.2 ⟨subd5_11_0, List.forall_mem_nil _⟩
theorem ld_okd6_0 : ldCheck G d6_0.U d6_0.ms ldd6_0 = true := by decide +kernel
theorem pre_okd6_0 : subPre G cell6 d6_0 = true := by decide +kernel
theorem subd6_0_0 : subd6_0 [] = true := by decide +kernel
theorem sbd6_0_0 : ∀ q ∈ blkd6_0_0, subd6_0 q = true := by
  unfold blkd6_0_0
  exact List.forall_mem_cons.2 ⟨subd6_0_0, List.forall_mem_nil _⟩
theorem ld_okd6_1 : ldCheck G d6_1.U d6_1.ms ldd6_1 = true := by decide +kernel
theorem pre_okd6_1 : subPre G cell6 d6_1 = true := by decide +kernel
theorem subd6_1_0 : subd6_1 [] = true := by decide +kernel
theorem sbd6_1_0 : ∀ q ∈ blkd6_1_0, subd6_1 q = true := by
  unfold blkd6_1_0
  exact List.forall_mem_cons.2 ⟨subd6_1_0, List.forall_mem_nil _⟩
theorem ld_okd6_2 : ldCheck G d6_2.U d6_2.ms ldd6_2 = true := by decide +kernel
theorem pre_okd6_2 : subPre G cell6 d6_2 = true := by decide +kernel
theorem subd6_2_0 : subd6_2 [] = true := by decide +kernel
theorem sbd6_2_0 : ∀ q ∈ blkd6_2_0, subd6_2 q = true := by
  unfold blkd6_2_0
  exact List.forall_mem_cons.2 ⟨subd6_2_0, List.forall_mem_nil _⟩
theorem ld_okd6_3 : ldCheck G d6_3.U d6_3.ms ldd6_3 = true := by decide +kernel
theorem pre_okd6_3 : subPre G cell6 d6_3 = true := by decide +kernel
theorem subd6_3_0 : subd6_3 [] = true := by decide +kernel
theorem sbd6_3_0 : ∀ q ∈ blkd6_3_0, subd6_3 q = true := by
  unfold blkd6_3_0
  exact List.forall_mem_cons.2 ⟨subd6_3_0, List.forall_mem_nil _⟩
theorem ld_okd6_4 : ldCheck G d6_4.U d6_4.ms ldd6_4 = true := by decide +kernel
theorem pre_okd6_4 : subPre G cell6 d6_4 = true := by decide +kernel
theorem subd6_4_0 : subd6_4 [-1, -2] = true := by decide +kernel
theorem subd6_4_1 : subd6_4 [-1, -1] = true := by decide +kernel
theorem subd6_4_2 : subd6_4 [-1, 0] = true := by decide +kernel
theorem subd6_4_3 : subd6_4 [-1, 1] = true := by decide +kernel
theorem subd6_4_4 : subd6_4 [-1, 2] = true := by decide +kernel
theorem subd6_4_5 : subd6_4 [0, -3] = true := by decide +kernel
theorem subd6_4_6 : subd6_4 [0, -2] = true := by decide +kernel
theorem subd6_4_7 : subd6_4 [0, -1] = true := by decide +kernel
theorem subd6_4_8 : subd6_4 [0, 0] = true := by decide +kernel
theorem subd6_4_9 : subd6_4 [0, 1] = true := by decide +kernel
theorem subd6_4_10 : subd6_4 [0, 2] = true := by decide +kernel
theorem subd6_4_11 : subd6_4 [1, -3] = true := by decide +kernel
theorem subd6_4_12 : subd6_4 [1, -2] = true := by decide +kernel
theorem subd6_4_13 : subd6_4 [1, -1] = true := by decide +kernel
theorem subd6_4_14 : subd6_4 [1, 0] = true := by decide +kernel
theorem subd6_4_15 : subd6_4 [1, 1] = true := by decide +kernel
theorem sbd6_4_0 : ∀ q ∈ blkd6_4_0, subd6_4 q = true := by
  unfold blkd6_4_0
  exact List.forall_mem_cons.2 ⟨subd6_4_0, List.forall_mem_cons.2 ⟨subd6_4_1, List.forall_mem_cons.2 ⟨subd6_4_2, List.forall_mem_cons.2 ⟨subd6_4_3, List.forall_mem_cons.2 ⟨subd6_4_4, List.forall_mem_cons.2 ⟨subd6_4_5, List.forall_mem_cons.2 ⟨subd6_4_6, List.forall_mem_cons.2 ⟨subd6_4_7, List.forall_mem_cons.2 ⟨subd6_4_8, List.forall_mem_cons.2 ⟨subd6_4_9, List.forall_mem_cons.2 ⟨subd6_4_10, List.forall_mem_cons.2 ⟨subd6_4_11, List.forall_mem_cons.2 ⟨subd6_4_12, List.forall_mem_cons.2 ⟨subd6_4_13, List.forall_mem_cons.2 ⟨subd6_4_14, List.forall_mem_cons.2 ⟨subd6_4_15, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_5 : ldCheck G d6_5.U d6_5.ms ldd6_5 = true := by decide +kernel
theorem pre_okd6_5 : subPre G cell6 d6_5 = true := by decide +kernel
theorem subd6_5_0 : subd6_5 [-1] = true := by decide +kernel
theorem subd6_5_1 : subd6_5 [0] = true := by decide +kernel
theorem subd6_5_2 : subd6_5 [1] = true := by decide +kernel
theorem sbd6_5_0 : ∀ q ∈ blkd6_5_0, subd6_5 q = true := by
  unfold blkd6_5_0
  exact List.forall_mem_cons.2 ⟨subd6_5_0, List.forall_mem_cons.2 ⟨subd6_5_1, List.forall_mem_cons.2 ⟨subd6_5_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd6_6 : ldCheck G d6_6.U d6_6.ms ldd6_6 = true := by decide +kernel
theorem pre_okd6_6 : subPre G cell6 d6_6 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C115
