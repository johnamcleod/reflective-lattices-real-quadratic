import ReflectZphi.Data.Cert5.C113.Base

namespace ReflectZphi.Data.Cert5.C113

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd4_6_0 : subd4_6 [-2] = true := by decide +kernel
theorem subd4_6_1 : subd4_6 [-1] = true := by decide +kernel
theorem subd4_6_2 : subd4_6 [0, -3] = true := by decide +kernel
theorem subd4_6_3 : subd4_6 [0, -2] = true := by decide +kernel
theorem subd4_6_4 : subd4_6 [0, -1] = true := by decide +kernel
theorem subd4_6_5 : subd4_6 [0, 0] = true := by decide +kernel
theorem subd4_6_6 : subd4_6 [0, 1] = true := by decide +kernel
theorem subd4_6_7 : subd4_6 [0, 2] = true := by decide +kernel
theorem subd4_6_8 : subd4_6 [1] = true := by decide +kernel
theorem subd4_6_9 : subd4_6 [2] = true := by decide +kernel
theorem sbd4_6_0 : ∀ q ∈ blkd4_6_0, subd4_6 q = true := by
  unfold blkd4_6_0
  exact List.forall_mem_cons.2 ⟨subd4_6_0, List.forall_mem_cons.2 ⟨subd4_6_1, List.forall_mem_cons.2 ⟨subd4_6_2, List.forall_mem_cons.2 ⟨subd4_6_3, List.forall_mem_cons.2 ⟨subd4_6_4, List.forall_mem_cons.2 ⟨subd4_6_5, List.forall_mem_cons.2 ⟨subd4_6_6, List.forall_mem_cons.2 ⟨subd4_6_7, List.forall_mem_cons.2 ⟨subd4_6_8, List.forall_mem_cons.2 ⟨subd4_6_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd4_7 : ldCheck G d4_7.U d4_7.ms ldd4_7 = true := by decide +kernel
theorem pre_okd4_7 : subPre G cell4 d4_7 = true := by decide +kernel
theorem subd4_7_0 : subd4_7 [-2] = true := by decide +kernel
theorem subd4_7_1 : subd4_7 [-1] = true := by decide +kernel
theorem subd4_7_2 : subd4_7 [0, -3] = true := by decide +kernel
theorem subd4_7_3 : subd4_7 [0, -2] = true := by decide +kernel
theorem subd4_7_4 : subd4_7 [0, -1] = true := by decide +kernel
theorem subd4_7_5 : subd4_7 [0, 0] = true := by decide +kernel
theorem subd4_7_6 : subd4_7 [0, 1] = true := by decide +kernel
theorem subd4_7_7 : subd4_7 [0, 2] = true := by decide +kernel
theorem subd4_7_8 : subd4_7 [1] = true := by decide +kernel
theorem subd4_7_9 : subd4_7 [2] = true := by decide +kernel
theorem sbd4_7_0 : ∀ q ∈ blkd4_7_0, subd4_7 q = true := by
  unfold blkd4_7_0
  exact List.forall_mem_cons.2 ⟨subd4_7_0, List.forall_mem_cons.2 ⟨subd4_7_1, List.forall_mem_cons.2 ⟨subd4_7_2, List.forall_mem_cons.2 ⟨subd4_7_3, List.forall_mem_cons.2 ⟨subd4_7_4, List.forall_mem_cons.2 ⟨subd4_7_5, List.forall_mem_cons.2 ⟨subd4_7_6, List.forall_mem_cons.2 ⟨subd4_7_7, List.forall_mem_cons.2 ⟨subd4_7_8, List.forall_mem_cons.2 ⟨subd4_7_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd4_8 : ldCheck G d4_8.U d4_8.ms ldd4_8 = true := by decide +kernel
theorem pre_okd4_8 : subPre G cell4 d4_8 = true := by decide +kernel
theorem subd4_8_0 : subd4_8 [-3] = true := by decide +kernel
theorem subd4_8_1 : subd4_8 [-2] = true := by decide +kernel
theorem subd4_8_2 : subd4_8 [-1] = true := by decide +kernel
theorem subd4_8_3 : subd4_8 [0, -4] = true := by decide +kernel
theorem subd4_8_4 : subd4_8 [0, -3] = true := by decide +kernel
theorem subd4_8_5 : subd4_8 [0, -2] = true := by decide +kernel
theorem subd4_8_6 : subd4_8 [0, -1] = true := by decide +kernel
theorem subd4_8_7 : subd4_8 [0, 0] = true := by decide +kernel
theorem subd4_8_8 : subd4_8 [0, 1] = true := by decide +kernel
theorem subd4_8_9 : subd4_8 [0, 2] = true := by decide +kernel
theorem subd4_8_10 : subd4_8 [0, 3] = true := by decide +kernel
theorem subd4_8_11 : subd4_8 [1] = true := by decide +kernel
theorem subd4_8_12 : subd4_8 [2] = true := by decide +kernel
theorem subd4_8_13 : subd4_8 [3] = true := by decide +kernel
theorem sbd4_8_0 : ∀ q ∈ blkd4_8_0, subd4_8 q = true := by
  unfold blkd4_8_0
  exact List.forall_mem_cons.2 ⟨subd4_8_0, List.forall_mem_cons.2 ⟨subd4_8_1, List.forall_mem_cons.2 ⟨subd4_8_2, List.forall_mem_cons.2 ⟨subd4_8_3, List.forall_mem_cons.2 ⟨subd4_8_4, List.forall_mem_cons.2 ⟨subd4_8_5, List.forall_mem_cons.2 ⟨subd4_8_6, List.forall_mem_cons.2 ⟨subd4_8_7, List.forall_mem_cons.2 ⟨subd4_8_8, List.forall_mem_cons.2 ⟨subd4_8_9, List.forall_mem_cons.2 ⟨subd4_8_10, List.forall_mem_cons.2 ⟨subd4_8_11, List.forall_mem_cons.2 ⟨subd4_8_12, List.forall_mem_cons.2 ⟨subd4_8_13, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd4_9 : ldCheck G d4_9.U d4_9.ms ldd4_9 = true := by decide +kernel
theorem pre_okd4_9 : subPre G cell4 d4_9 = true := by decide +kernel
theorem subd4_9_0 : subd4_9 [] = true := by decide +kernel
theorem sbd4_9_0 : ∀ q ∈ blkd4_9_0, subd4_9 q = true := by
  unfold blkd4_9_0
  exact List.forall_mem_cons.2 ⟨subd4_9_0, List.forall_mem_nil _⟩
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
theorem ld_okd5_3 : ldCheck G d5_3.U d5_3.ms ldd5_3 = true := by decide +kernel
theorem pre_okd5_3 : subPre G cell5 d5_3 = true := by decide +kernel
theorem subd5_3_0 : subd5_3 [] = true := by decide +kernel
theorem sbd5_3_0 : ∀ q ∈ blkd5_3_0, subd5_3 q = true := by
  unfold blkd5_3_0
  exact List.forall_mem_cons.2 ⟨subd5_3_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C113
