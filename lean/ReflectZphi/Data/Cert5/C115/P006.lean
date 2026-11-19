import ReflectZphi.Data.Cert5.C115.Base

namespace ReflectZphi.Data.Cert5.C115

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd4_6 : ldCheck G d4_6.U d4_6.ms ldd4_6 = true := by decide +kernel
theorem pre_okd4_6 : subPre G cell4 d4_6 = true := by decide +kernel
theorem subd4_6_0 : subd4_6 [-2] = true := by decide +kernel
theorem subd4_6_1 : subd4_6 [-1] = true := by decide +kernel
theorem subd4_6_2 : subd4_6 [0] = true := by decide +kernel
theorem subd4_6_3 : subd4_6 [1] = true := by decide +kernel
theorem subd4_6_4 : subd4_6 [2] = true := by decide +kernel
theorem sbd4_6_0 : ∀ q ∈ blkd4_6_0, subd4_6 q = true := by
  unfold blkd4_6_0
  exact List.forall_mem_cons.2 ⟨subd4_6_0, List.forall_mem_cons.2 ⟨subd4_6_1, List.forall_mem_cons.2 ⟨subd4_6_2, List.forall_mem_cons.2 ⟨subd4_6_3, List.forall_mem_cons.2 ⟨subd4_6_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd4_7 : ldCheck G d4_7.U d4_7.ms ldd4_7 = true := by decide +kernel
theorem pre_okd4_7 : subPre G cell4 d4_7 = true := by decide +kernel
theorem subd4_7_0 : subd4_7 [] = true := by decide +kernel
theorem sbd4_7_0 : ∀ q ∈ blkd4_7_0, subd4_7 q = true := by
  unfold blkd4_7_0
  exact List.forall_mem_cons.2 ⟨subd4_7_0, List.forall_mem_nil _⟩
theorem ld_okd4_8 : ldCheck G d4_8.U d4_8.ms ldd4_8 = true := by decide +kernel
theorem pre_okd4_8 : subPre G cell4 d4_8 = true := by decide +kernel
theorem subd4_8_0 : subd4_8 [] = true := by decide +kernel
theorem sbd4_8_0 : ∀ q ∈ blkd4_8_0, subd4_8 q = true := by
  unfold blkd4_8_0
  exact List.forall_mem_cons.2 ⟨subd4_8_0, List.forall_mem_nil _⟩
theorem ld_okd4_9 : ldCheck G d4_9.U d4_9.ms ldd4_9 = true := by decide +kernel
theorem pre_okd4_9 : subPre G cell4 d4_9 = true := by decide +kernel
theorem subd4_9_0 : subd4_9 [] = true := by decide +kernel
theorem sbd4_9_0 : ∀ q ∈ blkd4_9_0, subd4_9 q = true := by
  unfold blkd4_9_0
  exact List.forall_mem_cons.2 ⟨subd4_9_0, List.forall_mem_nil _⟩
theorem ld_okd4_10 : ldCheck G d4_10.U d4_10.ms ldd4_10 = true := by decide +kernel
theorem pre_okd4_10 : subPre G cell4 d4_10 = true := by decide +kernel
theorem subd4_10_0 : subd4_10 [] = true := by decide +kernel
theorem sbd4_10_0 : ∀ q ∈ blkd4_10_0, subd4_10 q = true := by
  unfold blkd4_10_0
  exact List.forall_mem_cons.2 ⟨subd4_10_0, List.forall_mem_nil _⟩
theorem ld_okd4_11 : ldCheck G d4_11.U d4_11.ms ldd4_11 = true := by decide +kernel
theorem pre_okd4_11 : subPre G cell4 d4_11 = true := by decide +kernel
theorem subd4_11_0 : subd4_11 [] = true := by decide +kernel
theorem sbd4_11_0 : ∀ q ∈ blkd4_11_0, subd4_11 q = true := by
  unfold blkd4_11_0
  exact List.forall_mem_cons.2 ⟨subd4_11_0, List.forall_mem_nil _⟩
theorem ld_okd5_0 : ldCheck G d5_0.U d5_0.ms ldd5_0 = true := by decide +kernel
theorem pre_okd5_0 : subPre G cell5 d5_0 = true := by decide +kernel
theorem subd5_0_0 : subd5_0 [] = true := by decide +kernel
theorem sbd5_0_0 : ∀ q ∈ blkd5_0_0, subd5_0 q = true := by
  unfold blkd5_0_0
  exact List.forall_mem_cons.2 ⟨subd5_0_0, List.forall_mem_nil _⟩
theorem ld_okd5_1 : ldCheck G d5_1.U d5_1.ms ldd5_1 = true := by decide +kernel
theorem pre_okd5_1 : subPre G cell5 d5_1 = true := by decide +kernel
theorem subd5_1_0 : subd5_1 [] = true := by decide +kernel
theorem sbd5_1_0 : ∀ q ∈ blkd5_1_0, subd5_1 q = true := by
  unfold blkd5_1_0
  exact List.forall_mem_cons.2 ⟨subd5_1_0, List.forall_mem_nil _⟩
theorem ld_okd5_2 : ldCheck G d5_2.U d5_2.ms ldd5_2 = true := by decide +kernel
theorem pre_okd5_2 : subPre G cell5 d5_2 = true := by decide +kernel
theorem subd5_2_0 : subd5_2 [] = true := by decide +kernel
theorem sbd5_2_0 : ∀ q ∈ blkd5_2_0, subd5_2 q = true := by
  unfold blkd5_2_0
  exact List.forall_mem_cons.2 ⟨subd5_2_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C115
