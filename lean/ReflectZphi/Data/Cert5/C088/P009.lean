import ReflectZphi.Data.Cert5.C088.Base

namespace ReflectZphi.Data.Cert5.C088

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd5_10 : ldCheck G d5_10.U d5_10.ms ldd5_10 = true := by decide +kernel
theorem pre_okd5_10 : subPre G cell5 d5_10 = true := by decide +kernel
theorem subd5_10_0 : subd5_10 [] = true := by decide +kernel
theorem sbd5_10_0 : ∀ q ∈ blkd5_10_0, subd5_10 q = true := by
  unfold blkd5_10_0
  exact List.forall_mem_cons.2 ⟨subd5_10_0, List.forall_mem_nil _⟩
theorem ld_okd5_11 : ldCheck G d5_11.U d5_11.ms ldd5_11 = true := by decide +kernel
theorem pre_okd5_11 : subPre G cell5 d5_11 = true := by decide +kernel
theorem subd5_11_0 : subd5_11 [-2] = true := by decide +kernel
theorem subd5_11_1 : subd5_11 [-1] = true := by decide +kernel
theorem subd5_11_2 : subd5_11 [0] = true := by decide +kernel
theorem subd5_11_3 : subd5_11 [1] = true := by decide +kernel
theorem subd5_11_4 : subd5_11 [2] = true := by decide +kernel
theorem sbd5_11_0 : ∀ q ∈ blkd5_11_0, subd5_11 q = true := by
  unfold blkd5_11_0
  exact List.forall_mem_cons.2 ⟨subd5_11_0, List.forall_mem_cons.2 ⟨subd5_11_1, List.forall_mem_cons.2 ⟨subd5_11_2, List.forall_mem_cons.2 ⟨subd5_11_3, List.forall_mem_cons.2 ⟨subd5_11_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd5_12 : ldCheck G d5_12.U d5_12.ms ldd5_12 = true := by decide +kernel
theorem pre_okd5_12 : subPre G cell5 d5_12 = true := by decide +kernel
theorem subd5_12_0 : subd5_12 [] = true := by decide +kernel
theorem sbd5_12_0 : ∀ q ∈ blkd5_12_0, subd5_12 q = true := by
  unfold blkd5_12_0
  exact List.forall_mem_cons.2 ⟨subd5_12_0, List.forall_mem_nil _⟩
theorem ld_okd5_13 : ldCheck G d5_13.U d5_13.ms ldd5_13 = true := by decide +kernel
theorem pre_okd5_13 : subPre G cell5 d5_13 = true := by decide +kernel
theorem subd5_13_0 : subd5_13 [] = true := by decide +kernel
theorem sbd5_13_0 : ∀ q ∈ blkd5_13_0, subd5_13 q = true := by
  unfold blkd5_13_0
  exact List.forall_mem_cons.2 ⟨subd5_13_0, List.forall_mem_nil _⟩
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
theorem subd6_4_0 : subd6_4 [] = true := by decide +kernel
theorem sbd6_4_0 : ∀ q ∈ blkd6_4_0, subd6_4 q = true := by
  unfold blkd6_4_0
  exact List.forall_mem_cons.2 ⟨subd6_4_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C088
