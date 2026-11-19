import ReflectZphi.Data.Cert5.C115.Base

namespace ReflectZphi.Data.Cert5.C115

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd5_3 : ldCheck G d5_3.U d5_3.ms ldd5_3 = true := by decide +kernel
theorem pre_okd5_3 : subPre G cell5 d5_3 = true := by decide +kernel
theorem subd5_3_0 : subd5_3 [] = true := by decide +kernel
theorem sbd5_3_0 : ∀ q ∈ blkd5_3_0, subd5_3 q = true := by
  unfold blkd5_3_0
  exact List.forall_mem_cons.2 ⟨subd5_3_0, List.forall_mem_nil _⟩
theorem ld_okd5_4 : ldCheck G d5_4.U d5_4.ms ldd5_4 = true := by decide +kernel
theorem pre_okd5_4 : subPre G cell5 d5_4 = true := by decide +kernel
theorem subd5_4_0 : subd5_4 [-1] = true := by decide +kernel
theorem subd5_4_1 : subd5_4 [0, -2] = true := by decide +kernel
theorem subd5_4_2 : subd5_4 [0, -1] = true := by decide +kernel
theorem subd5_4_3 : subd5_4 [0, 0] = true := by decide +kernel
theorem subd5_4_4 : subd5_4 [0, 1] = true := by decide +kernel
theorem subd5_4_5 : subd5_4 [1] = true := by decide +kernel
theorem sbd5_4_0 : ∀ q ∈ blkd5_4_0, subd5_4 q = true := by
  unfold blkd5_4_0
  exact List.forall_mem_cons.2 ⟨subd5_4_0, List.forall_mem_cons.2 ⟨subd5_4_1, List.forall_mem_cons.2 ⟨subd5_4_2, List.forall_mem_cons.2 ⟨subd5_4_3, List.forall_mem_cons.2 ⟨subd5_4_4, List.forall_mem_cons.2 ⟨subd5_4_5, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem ld_okd5_5 : ldCheck G d5_5.U d5_5.ms ldd5_5 = true := by decide +kernel
theorem pre_okd5_5 : subPre G cell5 d5_5 = true := by decide +kernel
theorem subd5_5_0 : subd5_5 [] = true := by decide +kernel
theorem sbd5_5_0 : ∀ q ∈ blkd5_5_0, subd5_5 q = true := by
  unfold blkd5_5_0
  exact List.forall_mem_cons.2 ⟨subd5_5_0, List.forall_mem_nil _⟩
theorem ld_okd5_6 : ldCheck G d5_6.U d5_6.ms ldd5_6 = true := by decide +kernel
theorem pre_okd5_6 : subPre G cell5 d5_6 = true := by decide +kernel
theorem subd5_6_0 : subd5_6 [-2] = true := by decide +kernel
theorem subd5_6_1 : subd5_6 [-1] = true := by decide +kernel
theorem subd5_6_2 : subd5_6 [0] = true := by decide +kernel
theorem subd5_6_3 : subd5_6 [1] = true := by decide +kernel
theorem subd5_6_4 : subd5_6 [2] = true := by decide +kernel
theorem sbd5_6_0 : ∀ q ∈ blkd5_6_0, subd5_6 q = true := by
  unfold blkd5_6_0
  exact List.forall_mem_cons.2 ⟨subd5_6_0, List.forall_mem_cons.2 ⟨subd5_6_1, List.forall_mem_cons.2 ⟨subd5_6_2, List.forall_mem_cons.2 ⟨subd5_6_3, List.forall_mem_cons.2 ⟨subd5_6_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd5_7 : ldCheck G d5_7.U d5_7.ms ldd5_7 = true := by decide +kernel
theorem pre_okd5_7 : subPre G cell5 d5_7 = true := by decide +kernel
theorem subd5_7_0 : subd5_7 [] = true := by decide +kernel
theorem sbd5_7_0 : ∀ q ∈ blkd5_7_0, subd5_7 q = true := by
  unfold blkd5_7_0
  exact List.forall_mem_cons.2 ⟨subd5_7_0, List.forall_mem_nil _⟩
theorem ld_okd5_8 : ldCheck G d5_8.U d5_8.ms ldd5_8 = true := by decide +kernel
theorem pre_okd5_8 : subPre G cell5 d5_8 = true := by decide +kernel
theorem subd5_8_0 : subd5_8 [-1] = true := by decide +kernel
theorem subd5_8_1 : subd5_8 [0] = true := by decide +kernel
theorem subd5_8_2 : subd5_8 [1] = true := by decide +kernel
theorem sbd5_8_0 : ∀ q ∈ blkd5_8_0, subd5_8 q = true := by
  unfold blkd5_8_0
  exact List.forall_mem_cons.2 ⟨subd5_8_0, List.forall_mem_cons.2 ⟨subd5_8_1, List.forall_mem_cons.2 ⟨subd5_8_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd5_9 : ldCheck G d5_9.U d5_9.ms ldd5_9 = true := by decide +kernel
theorem pre_okd5_9 : subPre G cell5 d5_9 = true := by decide +kernel
theorem subd5_9_0 : subd5_9 [] = true := by decide +kernel
theorem sbd5_9_0 : ∀ q ∈ blkd5_9_0, subd5_9 q = true := by
  unfold blkd5_9_0
  exact List.forall_mem_cons.2 ⟨subd5_9_0, List.forall_mem_nil _⟩
theorem ld_okd5_10 : ldCheck G d5_10.U d5_10.ms ldd5_10 = true := by decide +kernel
theorem pre_okd5_10 : subPre G cell5 d5_10 = true := by decide +kernel
theorem subd5_10_0 : subd5_10 [-1] = true := by decide +kernel
theorem subd5_10_1 : subd5_10 [0] = true := by decide +kernel
theorem subd5_10_2 : subd5_10 [1] = true := by decide +kernel
theorem sbd5_10_0 : ∀ q ∈ blkd5_10_0, subd5_10 q = true := by
  unfold blkd5_10_0
  exact List.forall_mem_cons.2 ⟨subd5_10_0, List.forall_mem_cons.2 ⟨subd5_10_1, List.forall_mem_cons.2 ⟨subd5_10_2, List.forall_mem_nil _⟩⟩⟩

end ReflectZphi.Data.Cert5.C115
