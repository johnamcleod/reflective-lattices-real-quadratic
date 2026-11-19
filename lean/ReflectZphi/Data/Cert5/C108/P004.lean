import ReflectZphi.Data.Cert5.C108.Base

namespace ReflectZphi.Data.Cert5.C108

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd4_4 : ldCheck G d4_4.U d4_4.ms ldd4_4 = true := by decide +kernel
theorem pre_okd4_4 : subPre G cell4 d4_4 = true := by decide +kernel
theorem subd4_4_0 : subd4_4 [-1] = true := by decide +kernel
theorem subd4_4_1 : subd4_4 [0] = true := by decide +kernel
theorem subd4_4_2 : subd4_4 [1] = true := by decide +kernel
theorem sbd4_4_0 : ∀ q ∈ blkd4_4_0, subd4_4 q = true := by
  unfold blkd4_4_0
  exact List.forall_mem_cons.2 ⟨subd4_4_0, List.forall_mem_cons.2 ⟨subd4_4_1, List.forall_mem_cons.2 ⟨subd4_4_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd4_5 : ldCheck G d4_5.U d4_5.ms ldd4_5 = true := by decide +kernel
theorem pre_okd4_5 : subPre G cell4 d4_5 = true := by decide +kernel
theorem subd4_5_0 : subd4_5 [] = true := by decide +kernel
theorem sbd4_5_0 : ∀ q ∈ blkd4_5_0, subd4_5 q = true := by
  unfold blkd4_5_0
  exact List.forall_mem_cons.2 ⟨subd4_5_0, List.forall_mem_nil _⟩
theorem ld_okd4_6 : ldCheck G d4_6.U d4_6.ms ldd4_6 = true := by decide +kernel
theorem pre_okd4_6 : subPre G cell4 d4_6 = true := by decide +kernel
theorem subd4_6_0 : subd4_6 [] = true := by decide +kernel
theorem sbd4_6_0 : ∀ q ∈ blkd4_6_0, subd4_6 q = true := by
  unfold blkd4_6_0
  exact List.forall_mem_cons.2 ⟨subd4_6_0, List.forall_mem_nil _⟩
theorem ld_okd4_7 : ldCheck G d4_7.U d4_7.ms ldd4_7 = true := by decide +kernel
theorem pre_okd4_7 : subPre G cell4 d4_7 = true := by decide +kernel
theorem subd4_7_0 : subd4_7 [] = true := by decide +kernel
theorem sbd4_7_0 : ∀ q ∈ blkd4_7_0, subd4_7 q = true := by
  unfold blkd4_7_0
  exact List.forall_mem_cons.2 ⟨subd4_7_0, List.forall_mem_nil _⟩
theorem ld_okd5_0 : ldCheck G d5_0.U d5_0.ms ldd5_0 = true := by decide +kernel
theorem pre_okd5_0 : subPre G cell5 d5_0 = true := by decide +kernel
theorem subd5_0_0 : subd5_0 [-2] = true := by decide +kernel
theorem subd5_0_1 : subd5_0 [-1] = true := by decide +kernel
theorem subd5_0_2 : subd5_0 [0] = true := by decide +kernel
theorem subd5_0_3 : subd5_0 [1] = true := by decide +kernel
theorem subd5_0_4 : subd5_0 [2] = true := by decide +kernel
theorem sbd5_0_0 : ∀ q ∈ blkd5_0_0, subd5_0 q = true := by
  unfold blkd5_0_0
  exact List.forall_mem_cons.2 ⟨subd5_0_0, List.forall_mem_cons.2 ⟨subd5_0_1, List.forall_mem_cons.2 ⟨subd5_0_2, List.forall_mem_cons.2 ⟨subd5_0_3, List.forall_mem_cons.2 ⟨subd5_0_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd5_1 : ldCheck G d5_1.U d5_1.ms ldd5_1 = true := by decide +kernel
theorem pre_okd5_1 : subPre G cell5 d5_1 = true := by decide +kernel
theorem subd5_1_0 : subd5_1 [-2] = true := by decide +kernel
theorem subd5_1_1 : subd5_1 [-1] = true := by decide +kernel
theorem subd5_1_2 : subd5_1 [0, -3] = true := by decide +kernel
theorem subd5_1_3 : subd5_1 [0, -2] = true := by decide +kernel
theorem subd5_1_4 : subd5_1 [0, -1] = true := by decide +kernel
theorem subd5_1_5 : subd5_1 [0, 0] = true := by decide +kernel
theorem subd5_1_6 : subd5_1 [0, 1] = true := by decide +kernel
theorem subd5_1_7 : subd5_1 [0, 2] = true := by decide +kernel
theorem subd5_1_8 : subd5_1 [1] = true := by decide +kernel
theorem subd5_1_9 : subd5_1 [2] = true := by decide +kernel
theorem sbd5_1_0 : ∀ q ∈ blkd5_1_0, subd5_1 q = true := by
  unfold blkd5_1_0
  exact List.forall_mem_cons.2 ⟨subd5_1_0, List.forall_mem_cons.2 ⟨subd5_1_1, List.forall_mem_cons.2 ⟨subd5_1_2, List.forall_mem_cons.2 ⟨subd5_1_3, List.forall_mem_cons.2 ⟨subd5_1_4, List.forall_mem_cons.2 ⟨subd5_1_5, List.forall_mem_cons.2 ⟨subd5_1_6, List.forall_mem_cons.2 ⟨subd5_1_7, List.forall_mem_cons.2 ⟨subd5_1_8, List.forall_mem_cons.2 ⟨subd5_1_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_2 : ldCheck G d5_2.U d5_2.ms ldd5_2 = true := by decide +kernel
theorem pre_okd5_2 : subPre G cell5 d5_2 = true := by decide +kernel
theorem subd5_2_0 : subd5_2 [0, -2] = true := by decide +kernel
theorem subd5_2_1 : subd5_2 [0, -1] = true := by decide +kernel
theorem subd5_2_2 : subd5_2 [0, 0, -8] = true := by decide +kernel
theorem subd5_2_3 : subd5_2 [0, 0, -7] = true := by decide +kernel
theorem subd5_2_4 : subd5_2 [0, 0, -6] = true := by decide +kernel
theorem subd5_2_5 : subd5_2 [0, 0, -5] = true := by decide +kernel
theorem subd5_2_6 : subd5_2 [0, 0, -4] = true := by decide +kernel
theorem subd5_2_7 : subd5_2 [0, 0, -3] = true := by decide +kernel
theorem subd5_2_8 : subd5_2 [0, 0, -2] = true := by decide +kernel
theorem subd5_2_9 : subd5_2 [0, 0, -1] = true := by decide +kernel
theorem subd5_2_10 : subd5_2 [0, 0, 0] = true := by decide +kernel
theorem subd5_2_11 : subd5_2 [0, 0, 1] = true := by decide +kernel
theorem subd5_2_12 : subd5_2 [0, 0, 2] = true := by decide +kernel
theorem subd5_2_13 : subd5_2 [0, 0, 3] = true := by decide +kernel
theorem subd5_2_14 : subd5_2 [0, 0, 4] = true := by decide +kernel
theorem subd5_2_15 : subd5_2 [0, 0, 5] = true := by decide +kernel
theorem subd5_2_16 : subd5_2 [0, 0, 6] = true := by decide +kernel
theorem subd5_2_17 : subd5_2 [0, 0, 7] = true := by decide +kernel
theorem subd5_2_18 : subd5_2 [0, 1] = true := by decide +kernel
theorem sbd5_2_0 : ∀ q ∈ blkd5_2_0, subd5_2 q = true := by
  unfold blkd5_2_0
  exact List.forall_mem_cons.2 ⟨subd5_2_0, List.forall_mem_cons.2 ⟨subd5_2_1, List.forall_mem_cons.2 ⟨subd5_2_2, List.forall_mem_cons.2 ⟨subd5_2_3, List.forall_mem_cons.2 ⟨subd5_2_4, List.forall_mem_cons.2 ⟨subd5_2_5, List.forall_mem_cons.2 ⟨subd5_2_6, List.forall_mem_cons.2 ⟨subd5_2_7, List.forall_mem_cons.2 ⟨subd5_2_8, List.forall_mem_cons.2 ⟨subd5_2_9, List.forall_mem_cons.2 ⟨subd5_2_10, List.forall_mem_cons.2 ⟨subd5_2_11, List.forall_mem_cons.2 ⟨subd5_2_12, List.forall_mem_cons.2 ⟨subd5_2_13, List.forall_mem_cons.2 ⟨subd5_2_14, List.forall_mem_cons.2 ⟨subd5_2_15, List.forall_mem_cons.2 ⟨subd5_2_16, List.forall_mem_cons.2 ⟨subd5_2_17, List.forall_mem_cons.2 ⟨subd5_2_18, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_3 : ldCheck G d5_3.U d5_3.ms ldd5_3 = true := by decide +kernel
theorem pre_okd5_3 : subPre G cell5 d5_3 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C108
