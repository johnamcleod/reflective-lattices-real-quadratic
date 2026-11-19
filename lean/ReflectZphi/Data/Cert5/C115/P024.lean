import ReflectZphi.Data.Cert5.C115.Base

namespace ReflectZphi.Data.Cert5.C115

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd15_5 : ldCheck G d15_5.U d15_5.ms ldd15_5 = true := by decide +kernel
theorem pre_okd15_5 : subPre G cell15 d15_5 = true := by decide +kernel
theorem subd15_5_0 : subd15_5 [-2] = true := by decide +kernel
theorem subd15_5_1 : subd15_5 [-1] = true := by decide +kernel
theorem subd15_5_2 : subd15_5 [0] = true := by decide +kernel
theorem subd15_5_3 : subd15_5 [1] = true := by decide +kernel
theorem subd15_5_4 : subd15_5 [2] = true := by decide +kernel
theorem sbd15_5_0 : ∀ q ∈ blkd15_5_0, subd15_5 q = true := by
  unfold blkd15_5_0
  exact List.forall_mem_cons.2 ⟨subd15_5_0, List.forall_mem_cons.2 ⟨subd15_5_1, List.forall_mem_cons.2 ⟨subd15_5_2, List.forall_mem_cons.2 ⟨subd15_5_3, List.forall_mem_cons.2 ⟨subd15_5_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd15_6 : ldCheck G d15_6.U d15_6.ms ldd15_6 = true := by decide +kernel
theorem pre_okd15_6 : subPre G cell15 d15_6 = true := by decide +kernel
theorem subd15_6_0 : subd15_6 [-2] = true := by decide +kernel
theorem subd15_6_1 : subd15_6 [-1, -3] = true := by decide +kernel
theorem subd15_6_2 : subd15_6 [-1, -2] = true := by decide +kernel
theorem subd15_6_3 : subd15_6 [-1, -1] = true := by decide +kernel
theorem subd15_6_4 : subd15_6 [-1, 0] = true := by decide +kernel
theorem subd15_6_5 : subd15_6 [-1, 1] = true := by decide +kernel
theorem subd15_6_6 : subd15_6 [-1, 2] = true := by decide +kernel
theorem subd15_6_7 : subd15_6 [0, -3] = true := by decide +kernel
theorem subd15_6_8 : subd15_6 [0, -2] = true := by decide +kernel
theorem subd15_6_9 : subd15_6 [0, -1] = true := by decide +kernel
theorem subd15_6_10 : subd15_6 [0, 0] = true := by decide +kernel
theorem subd15_6_11 : subd15_6 [0, 1] = true := by decide +kernel
theorem subd15_6_12 : subd15_6 [0, 2] = true := by decide +kernel
theorem subd15_6_13 : subd15_6 [1, -3] = true := by decide +kernel
theorem subd15_6_14 : subd15_6 [1, -2] = true := by decide +kernel
theorem subd15_6_15 : subd15_6 [1, -1] = true := by decide +kernel
theorem subd15_6_16 : subd15_6 [1, 0] = true := by decide +kernel
theorem subd15_6_17 : subd15_6 [1, 1] = true := by decide +kernel
theorem subd15_6_18 : subd15_6 [1, 2] = true := by decide +kernel
theorem subd15_6_19 : subd15_6 [2] = true := by decide +kernel
theorem sbd15_6_0 : ∀ q ∈ blkd15_6_0, subd15_6 q = true := by
  unfold blkd15_6_0
  exact List.forall_mem_cons.2 ⟨subd15_6_0, List.forall_mem_cons.2 ⟨subd15_6_1, List.forall_mem_cons.2 ⟨subd15_6_2, List.forall_mem_cons.2 ⟨subd15_6_3, List.forall_mem_cons.2 ⟨subd15_6_4, List.forall_mem_cons.2 ⟨subd15_6_5, List.forall_mem_cons.2 ⟨subd15_6_6, List.forall_mem_cons.2 ⟨subd15_6_7, List.forall_mem_cons.2 ⟨subd15_6_8, List.forall_mem_cons.2 ⟨subd15_6_9, List.forall_mem_cons.2 ⟨subd15_6_10, List.forall_mem_cons.2 ⟨subd15_6_11, List.forall_mem_cons.2 ⟨subd15_6_12, List.forall_mem_cons.2 ⟨subd15_6_13, List.forall_mem_cons.2 ⟨subd15_6_14, List.forall_mem_cons.2 ⟨subd15_6_15, List.forall_mem_cons.2 ⟨subd15_6_16, List.forall_mem_cons.2 ⟨subd15_6_17, List.forall_mem_cons.2 ⟨subd15_6_18, List.forall_mem_cons.2 ⟨subd15_6_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd15_7 : ldCheck G d15_7.U d15_7.ms ldd15_7 = true := by decide +kernel
theorem pre_okd15_7 : subPre G cell15 d15_7 = true := by decide +kernel
theorem subd15_7_0 : subd15_7 [-1] = true := by decide +kernel
theorem subd15_7_1 : subd15_7 [0, -2] = true := by decide +kernel
theorem subd15_7_2 : subd15_7 [0, -1] = true := by decide +kernel
theorem subd15_7_3 : subd15_7 [0, 0] = true := by decide +kernel
theorem subd15_7_4 : subd15_7 [0, 1] = true := by decide +kernel
theorem subd15_7_5 : subd15_7 [1] = true := by decide +kernel
theorem sbd15_7_0 : ∀ q ∈ blkd15_7_0, subd15_7 q = true := by
  unfold blkd15_7_0
  exact List.forall_mem_cons.2 ⟨subd15_7_0, List.forall_mem_cons.2 ⟨subd15_7_1, List.forall_mem_cons.2 ⟨subd15_7_2, List.forall_mem_cons.2 ⟨subd15_7_3, List.forall_mem_cons.2 ⟨subd15_7_4, List.forall_mem_cons.2 ⟨subd15_7_5, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem ld_okd15_8 : ldCheck G d15_8.U d15_8.ms ldd15_8 = true := by decide +kernel
theorem pre_okd15_8 : subPre G cell15 d15_8 = true := by decide +kernel
theorem subd15_8_0 : subd15_8 [-2] = true := by decide +kernel
theorem subd15_8_1 : subd15_8 [-1] = true := by decide +kernel
theorem subd15_8_2 : subd15_8 [0, -3] = true := by decide +kernel
theorem subd15_8_3 : subd15_8 [0, -2] = true := by decide +kernel
theorem subd15_8_4 : subd15_8 [0, -1] = true := by decide +kernel
theorem subd15_8_5 : subd15_8 [0, 0] = true := by decide +kernel
theorem subd15_8_6 : subd15_8 [0, 1] = true := by decide +kernel
theorem subd15_8_7 : subd15_8 [0, 2] = true := by decide +kernel
theorem subd15_8_8 : subd15_8 [1] = true := by decide +kernel
theorem subd15_8_9 : subd15_8 [2] = true := by decide +kernel
theorem sbd15_8_0 : ∀ q ∈ blkd15_8_0, subd15_8 q = true := by
  unfold blkd15_8_0
  exact List.forall_mem_cons.2 ⟨subd15_8_0, List.forall_mem_cons.2 ⟨subd15_8_1, List.forall_mem_cons.2 ⟨subd15_8_2, List.forall_mem_cons.2 ⟨subd15_8_3, List.forall_mem_cons.2 ⟨subd15_8_4, List.forall_mem_cons.2 ⟨subd15_8_5, List.forall_mem_cons.2 ⟨subd15_8_6, List.forall_mem_cons.2 ⟨subd15_8_7, List.forall_mem_cons.2 ⟨subd15_8_8, List.forall_mem_cons.2 ⟨subd15_8_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd15_9 : ldCheck G d15_9.U d15_9.ms ldd15_9 = true := by decide +kernel
theorem pre_okd15_9 : subPre G cell15 d15_9 = true := by decide +kernel
theorem subd15_9_0 : subd15_9 [] = true := by decide +kernel
theorem sbd15_9_0 : ∀ q ∈ blkd15_9_0, subd15_9 q = true := by
  unfold blkd15_9_0
  exact List.forall_mem_cons.2 ⟨subd15_9_0, List.forall_mem_nil _⟩
theorem ld_okd15_10 : ldCheck G d15_10.U d15_10.ms ldd15_10 = true := by decide +kernel
theorem pre_okd15_10 : subPre G cell15 d15_10 = true := by decide +kernel
theorem subd15_10_0 : subd15_10 [-2] = true := by decide +kernel
theorem subd15_10_1 : subd15_10 [-1] = true := by decide +kernel
theorem subd15_10_2 : subd15_10 [0] = true := by decide +kernel
theorem subd15_10_3 : subd15_10 [1] = true := by decide +kernel
theorem subd15_10_4 : subd15_10 [2] = true := by decide +kernel
theorem sbd15_10_0 : ∀ q ∈ blkd15_10_0, subd15_10 q = true := by
  unfold blkd15_10_0
  exact List.forall_mem_cons.2 ⟨subd15_10_0, List.forall_mem_cons.2 ⟨subd15_10_1, List.forall_mem_cons.2 ⟨subd15_10_2, List.forall_mem_cons.2 ⟨subd15_10_3, List.forall_mem_cons.2 ⟨subd15_10_4, List.forall_mem_nil _⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C115
