import ReflectZphi.Data.Cert5.C088.Base

namespace ReflectZphi.Data.Cert5.C088

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

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
theorem ld_okd5_3 : ldCheck G d5_3.U d5_3.ms ldd5_3 = true := by decide +kernel
theorem pre_okd5_3 : subPre G cell5 d5_3 = true := by decide +kernel
theorem subd5_3_0 : subd5_3 [] = true := by decide +kernel
theorem sbd5_3_0 : ∀ q ∈ blkd5_3_0, subd5_3 q = true := by
  unfold blkd5_3_0
  exact List.forall_mem_cons.2 ⟨subd5_3_0, List.forall_mem_nil _⟩
theorem ld_okd5_4 : ldCheck G d5_4.U d5_4.ms ldd5_4 = true := by decide +kernel
theorem pre_okd5_4 : subPre G cell5 d5_4 = true := by decide +kernel
theorem subd5_4_0 : subd5_4 [] = true := by decide +kernel
theorem sbd5_4_0 : ∀ q ∈ blkd5_4_0, subd5_4 q = true := by
  unfold blkd5_4_0
  exact List.forall_mem_cons.2 ⟨subd5_4_0, List.forall_mem_nil _⟩
theorem ld_okd5_5 : ldCheck G d5_5.U d5_5.ms ldd5_5 = true := by decide +kernel
theorem pre_okd5_5 : subPre G cell5 d5_5 = true := by decide +kernel
theorem subd5_5_0 : subd5_5 [] = true := by decide +kernel
theorem sbd5_5_0 : ∀ q ∈ blkd5_5_0, subd5_5 q = true := by
  unfold blkd5_5_0
  exact List.forall_mem_cons.2 ⟨subd5_5_0, List.forall_mem_nil _⟩
theorem ld_okd5_6 : ldCheck G d5_6.U d5_6.ms ldd5_6 = true := by decide +kernel
theorem pre_okd5_6 : subPre G cell5 d5_6 = true := by decide +kernel
theorem subd5_6_0 : subd5_6 [] = true := by decide +kernel
theorem sbd5_6_0 : ∀ q ∈ blkd5_6_0, subd5_6 q = true := by
  unfold blkd5_6_0
  exact List.forall_mem_cons.2 ⟨subd5_6_0, List.forall_mem_nil _⟩
theorem ld_okd5_7 : ldCheck G d5_7.U d5_7.ms ldd5_7 = true := by decide +kernel
theorem pre_okd5_7 : subPre G cell5 d5_7 = true := by decide +kernel
theorem subd5_7_0 : subd5_7 [-2] = true := by decide +kernel
theorem subd5_7_1 : subd5_7 [-1] = true := by decide +kernel
theorem subd5_7_2 : subd5_7 [0] = true := by decide +kernel
theorem subd5_7_3 : subd5_7 [1] = true := by decide +kernel
theorem subd5_7_4 : subd5_7 [2] = true := by decide +kernel
theorem sbd5_7_0 : ∀ q ∈ blkd5_7_0, subd5_7 q = true := by
  unfold blkd5_7_0
  exact List.forall_mem_cons.2 ⟨subd5_7_0, List.forall_mem_cons.2 ⟨subd5_7_1, List.forall_mem_cons.2 ⟨subd5_7_2, List.forall_mem_cons.2 ⟨subd5_7_3, List.forall_mem_cons.2 ⟨subd5_7_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd5_8 : ldCheck G d5_8.U d5_8.ms ldd5_8 = true := by decide +kernel
theorem pre_okd5_8 : subPre G cell5 d5_8 = true := by decide +kernel
theorem subd5_8_0 : subd5_8 [] = true := by decide +kernel
theorem sbd5_8_0 : ∀ q ∈ blkd5_8_0, subd5_8 q = true := by
  unfold blkd5_8_0
  exact List.forall_mem_cons.2 ⟨subd5_8_0, List.forall_mem_nil _⟩
theorem ld_okd5_9 : ldCheck G d5_9.U d5_9.ms ldd5_9 = true := by decide +kernel
theorem pre_okd5_9 : subPre G cell5 d5_9 = true := by decide +kernel
theorem subd5_9_0 : subd5_9 [] = true := by decide +kernel
theorem sbd5_9_0 : ∀ q ∈ blkd5_9_0, subd5_9 q = true := by
  unfold blkd5_9_0
  exact List.forall_mem_cons.2 ⟨subd5_9_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C088
