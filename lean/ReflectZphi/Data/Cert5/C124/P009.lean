import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd4_9_0 : subd4_9 [-1, -2] = true := by decide +kernel
theorem subd4_9_1 : subd4_9 [-1, -1] = true := by decide +kernel
theorem subd4_9_2 : subd4_9 [-1, 0] = true := by decide +kernel
theorem subd4_9_3 : subd4_9 [-1, 1] = true := by decide +kernel
theorem subd4_9_4 : subd4_9 [0, -2] = true := by decide +kernel
theorem subd4_9_5 : subd4_9 [0, -1] = true := by decide +kernel
theorem subd4_9_6 : subd4_9 [0, 0] = true := by decide +kernel
theorem subd4_9_7 : subd4_9 [0, 1] = true := by decide +kernel
theorem subd4_9_8 : subd4_9 [1, -2] = true := by decide +kernel
theorem subd4_9_9 : subd4_9 [1, -1] = true := by decide +kernel
theorem subd4_9_10 : subd4_9 [1, 0] = true := by decide +kernel
theorem subd4_9_11 : subd4_9 [1, 1] = true := by decide +kernel
theorem sbd4_9_0 : ∀ q ∈ blkd4_9_0, subd4_9 q = true := by
  unfold blkd4_9_0
  exact List.forall_mem_cons.2 ⟨subd4_9_0, List.forall_mem_cons.2 ⟨subd4_9_1, List.forall_mem_cons.2 ⟨subd4_9_2, List.forall_mem_cons.2 ⟨subd4_9_3, List.forall_mem_cons.2 ⟨subd4_9_4, List.forall_mem_cons.2 ⟨subd4_9_5, List.forall_mem_cons.2 ⟨subd4_9_6, List.forall_mem_cons.2 ⟨subd4_9_7, List.forall_mem_cons.2 ⟨subd4_9_8, List.forall_mem_cons.2 ⟨subd4_9_9, List.forall_mem_cons.2 ⟨subd4_9_10, List.forall_mem_cons.2 ⟨subd4_9_11, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd4_10 : ldCheck G d4_10.U d4_10.ms ldd4_10 = true := by decide +kernel
theorem pre_okd4_10 : subPre G cell4 d4_10 = true := by decide +kernel
theorem subd4_10_0 : subd4_10 [-2] = true := by decide +kernel
theorem subd4_10_1 : subd4_10 [-1] = true := by decide +kernel
theorem subd4_10_2 : subd4_10 [0] = true := by decide +kernel
theorem subd4_10_3 : subd4_10 [1] = true := by decide +kernel
theorem subd4_10_4 : subd4_10 [2] = true := by decide +kernel
theorem sbd4_10_0 : ∀ q ∈ blkd4_10_0, subd4_10 q = true := by
  unfold blkd4_10_0
  exact List.forall_mem_cons.2 ⟨subd4_10_0, List.forall_mem_cons.2 ⟨subd4_10_1, List.forall_mem_cons.2 ⟨subd4_10_2, List.forall_mem_cons.2 ⟨subd4_10_3, List.forall_mem_cons.2 ⟨subd4_10_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd4_11 : ldCheck G d4_11.U d4_11.ms ldd4_11 = true := by decide +kernel
theorem pre_okd4_11 : subPre G cell4 d4_11 = true := by decide +kernel
theorem subd4_11_0 : subd4_11 [-2] = true := by decide +kernel
theorem subd4_11_1 : subd4_11 [-1] = true := by decide +kernel
theorem subd4_11_2 : subd4_11 [0] = true := by decide +kernel
theorem subd4_11_3 : subd4_11 [1] = true := by decide +kernel
theorem subd4_11_4 : subd4_11 [2] = true := by decide +kernel
theorem sbd4_11_0 : ∀ q ∈ blkd4_11_0, subd4_11 q = true := by
  unfold blkd4_11_0
  exact List.forall_mem_cons.2 ⟨subd4_11_0, List.forall_mem_cons.2 ⟨subd4_11_1, List.forall_mem_cons.2 ⟨subd4_11_2, List.forall_mem_cons.2 ⟨subd4_11_3, List.forall_mem_cons.2 ⟨subd4_11_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd4_12 : ldCheck G d4_12.U d4_12.ms ldd4_12 = true := by decide +kernel
theorem pre_okd4_12 : subPre G cell4 d4_12 = true := by decide +kernel
theorem subd4_12_0 : subd4_12 [-1] = true := by decide +kernel
theorem subd4_12_1 : subd4_12 [0] = true := by decide +kernel
theorem subd4_12_2 : subd4_12 [1] = true := by decide +kernel
theorem sbd4_12_0 : ∀ q ∈ blkd4_12_0, subd4_12 q = true := by
  unfold blkd4_12_0
  exact List.forall_mem_cons.2 ⟨subd4_12_0, List.forall_mem_cons.2 ⟨subd4_12_1, List.forall_mem_cons.2 ⟨subd4_12_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd4_13 : ldCheck G d4_13.U d4_13.ms ldd4_13 = true := by decide +kernel
theorem pre_okd4_13 : subPre G cell4 d4_13 = true := by decide +kernel
theorem subd4_13_0 : subd4_13 [] = true := by decide +kernel
theorem sbd4_13_0 : ∀ q ∈ blkd4_13_0, subd4_13 q = true := by
  unfold blkd4_13_0
  exact List.forall_mem_cons.2 ⟨subd4_13_0, List.forall_mem_nil _⟩
theorem ld_okd4_14 : ldCheck G d4_14.U d4_14.ms ldd4_14 = true := by decide +kernel
theorem pre_okd4_14 : subPre G cell4 d4_14 = true := by decide +kernel
theorem subd4_14_0 : subd4_14 [-3] = true := by decide +kernel
theorem subd4_14_1 : subd4_14 [-2] = true := by decide +kernel
theorem subd4_14_2 : subd4_14 [-1, -3] = true := by decide +kernel
theorem subd4_14_3 : subd4_14 [-1, -2] = true := by decide +kernel
theorem subd4_14_4 : subd4_14 [-1, -1] = true := by decide +kernel
theorem subd4_14_5 : subd4_14 [-1, 0] = true := by decide +kernel
theorem subd4_14_6 : subd4_14 [-1, 1] = true := by decide +kernel
theorem subd4_14_7 : subd4_14 [-1, 2] = true := by decide +kernel
theorem subd4_14_8 : subd4_14 [0, -3] = true := by decide +kernel
theorem subd4_14_9 : subd4_14 [0, -2] = true := by decide +kernel
theorem subd4_14_10 : subd4_14 [0, -1] = true := by decide +kernel
theorem subd4_14_11 : subd4_14 [0, 0] = true := by decide +kernel
theorem subd4_14_12 : subd4_14 [0, 1] = true := by decide +kernel
theorem subd4_14_13 : subd4_14 [0, 2] = true := by decide +kernel
theorem subd4_14_14 : subd4_14 [1, -3] = true := by decide +kernel
theorem subd4_14_15 : subd4_14 [1, -2] = true := by decide +kernel
theorem subd4_14_16 : subd4_14 [1, -1] = true := by decide +kernel
theorem subd4_14_17 : subd4_14 [1, 0] = true := by decide +kernel
theorem subd4_14_18 : subd4_14 [1, 1] = true := by decide +kernel
theorem subd4_14_19 : subd4_14 [1, 2] = true := by decide +kernel
theorem subd4_14_20 : subd4_14 [2] = true := by decide +kernel
theorem subd4_14_21 : subd4_14 [3] = true := by decide +kernel
theorem sbd4_14_0 : ∀ q ∈ blkd4_14_0, subd4_14 q = true := by
  unfold blkd4_14_0
  exact List.forall_mem_cons.2 ⟨subd4_14_0, List.forall_mem_cons.2 ⟨subd4_14_1, List.forall_mem_cons.2 ⟨subd4_14_2, List.forall_mem_cons.2 ⟨subd4_14_3, List.forall_mem_cons.2 ⟨subd4_14_4, List.forall_mem_cons.2 ⟨subd4_14_5, List.forall_mem_cons.2 ⟨subd4_14_6, List.forall_mem_cons.2 ⟨subd4_14_7, List.forall_mem_cons.2 ⟨subd4_14_8, List.forall_mem_cons.2 ⟨subd4_14_9, List.forall_mem_cons.2 ⟨subd4_14_10, List.forall_mem_cons.2 ⟨subd4_14_11, List.forall_mem_cons.2 ⟨subd4_14_12, List.forall_mem_cons.2 ⟨subd4_14_13, List.forall_mem_cons.2 ⟨subd4_14_14, List.forall_mem_cons.2 ⟨subd4_14_15, List.forall_mem_cons.2 ⟨subd4_14_16, List.forall_mem_cons.2 ⟨subd4_14_17, List.forall_mem_cons.2 ⟨subd4_14_18, List.forall_mem_cons.2 ⟨subd4_14_19, List.forall_mem_cons.2 ⟨subd4_14_20, List.forall_mem_cons.2 ⟨subd4_14_21, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_0 : ldCheck G d5_0.U d5_0.ms ldd5_0 = true := by decide +kernel
theorem pre_okd5_0 : subPre G cell5 d5_0 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C124
