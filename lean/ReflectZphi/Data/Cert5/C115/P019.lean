import ReflectZphi.Data.Cert5.C115.Base

namespace ReflectZphi.Data.Cert5.C115

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd12_7 : ldCheck G d12_7.U d12_7.ms ldd12_7 = true := by decide +kernel
theorem pre_okd12_7 : subPre G cell12 d12_7 = true := by decide +kernel
theorem subd12_7_0 : subd12_7 [-2] = true := by decide +kernel
theorem subd12_7_1 : subd12_7 [-1] = true := by decide +kernel
theorem subd12_7_2 : subd12_7 [0] = true := by decide +kernel
theorem subd12_7_3 : subd12_7 [1] = true := by decide +kernel
theorem subd12_7_4 : subd12_7 [2] = true := by decide +kernel
theorem sbd12_7_0 : ∀ q ∈ blkd12_7_0, subd12_7 q = true := by
  unfold blkd12_7_0
  exact List.forall_mem_cons.2 ⟨subd12_7_0, List.forall_mem_cons.2 ⟨subd12_7_1, List.forall_mem_cons.2 ⟨subd12_7_2, List.forall_mem_cons.2 ⟨subd12_7_3, List.forall_mem_cons.2 ⟨subd12_7_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd12_8 : ldCheck G d12_8.U d12_8.ms ldd12_8 = true := by decide +kernel
theorem pre_okd12_8 : subPre G cell12 d12_8 = true := by decide +kernel
theorem subd12_8_0 : subd12_8 [-2] = true := by decide +kernel
theorem subd12_8_1 : subd12_8 [-1, -3] = true := by decide +kernel
theorem subd12_8_2 : subd12_8 [-1, -2] = true := by decide +kernel
theorem subd12_8_3 : subd12_8 [-1, -1] = true := by decide +kernel
theorem subd12_8_4 : subd12_8 [-1, 0] = true := by decide +kernel
theorem subd12_8_5 : subd12_8 [-1, 1] = true := by decide +kernel
theorem subd12_8_6 : subd12_8 [-1, 2] = true := by decide +kernel
theorem subd12_8_7 : subd12_8 [0, -3] = true := by decide +kernel
theorem subd12_8_8 : subd12_8 [0, -2] = true := by decide +kernel
theorem subd12_8_9 : subd12_8 [0, -1] = true := by decide +kernel
theorem subd12_8_10 : subd12_8 [0, 0] = true := by decide +kernel
theorem subd12_8_11 : subd12_8 [0, 1] = true := by decide +kernel
theorem subd12_8_12 : subd12_8 [0, 2] = true := by decide +kernel
theorem subd12_8_13 : subd12_8 [1, -3] = true := by decide +kernel
theorem subd12_8_14 : subd12_8 [1, -2] = true := by decide +kernel
theorem subd12_8_15 : subd12_8 [1, -1] = true := by decide +kernel
theorem subd12_8_16 : subd12_8 [1, 0] = true := by decide +kernel
theorem subd12_8_17 : subd12_8 [1, 1] = true := by decide +kernel
theorem subd12_8_18 : subd12_8 [1, 2] = true := by decide +kernel
theorem subd12_8_19 : subd12_8 [2] = true := by decide +kernel
theorem sbd12_8_0 : ∀ q ∈ blkd12_8_0, subd12_8 q = true := by
  unfold blkd12_8_0
  exact List.forall_mem_cons.2 ⟨subd12_8_0, List.forall_mem_cons.2 ⟨subd12_8_1, List.forall_mem_cons.2 ⟨subd12_8_2, List.forall_mem_cons.2 ⟨subd12_8_3, List.forall_mem_cons.2 ⟨subd12_8_4, List.forall_mem_cons.2 ⟨subd12_8_5, List.forall_mem_cons.2 ⟨subd12_8_6, List.forall_mem_cons.2 ⟨subd12_8_7, List.forall_mem_cons.2 ⟨subd12_8_8, List.forall_mem_cons.2 ⟨subd12_8_9, List.forall_mem_cons.2 ⟨subd12_8_10, List.forall_mem_cons.2 ⟨subd12_8_11, List.forall_mem_cons.2 ⟨subd12_8_12, List.forall_mem_cons.2 ⟨subd12_8_13, List.forall_mem_cons.2 ⟨subd12_8_14, List.forall_mem_cons.2 ⟨subd12_8_15, List.forall_mem_cons.2 ⟨subd12_8_16, List.forall_mem_cons.2 ⟨subd12_8_17, List.forall_mem_cons.2 ⟨subd12_8_18, List.forall_mem_cons.2 ⟨subd12_8_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd12_9 : ldCheck G d12_9.U d12_9.ms ldd12_9 = true := by decide +kernel
theorem pre_okd12_9 : subPre G cell12 d12_9 = true := by decide +kernel
theorem subd12_9_0 : subd12_9 [] = true := by decide +kernel
theorem sbd12_9_0 : ∀ q ∈ blkd12_9_0, subd12_9 q = true := by
  unfold blkd12_9_0
  exact List.forall_mem_cons.2 ⟨subd12_9_0, List.forall_mem_nil _⟩
theorem ld_okd12_10 : ldCheck G d12_10.U d12_10.ms ldd12_10 = true := by decide +kernel
theorem pre_okd12_10 : subPre G cell12 d12_10 = true := by decide +kernel
theorem subd12_10_0 : subd12_10 [-2] = true := by decide +kernel
theorem subd12_10_1 : subd12_10 [-1] = true := by decide +kernel
theorem subd12_10_2 : subd12_10 [0, -3] = true := by decide +kernel
theorem subd12_10_3 : subd12_10 [0, -2] = true := by decide +kernel
theorem subd12_10_4 : subd12_10 [0, -1] = true := by decide +kernel
theorem subd12_10_5 : subd12_10 [0, 0] = true := by decide +kernel
theorem subd12_10_6 : subd12_10 [0, 1] = true := by decide +kernel
theorem subd12_10_7 : subd12_10 [0, 2] = true := by decide +kernel
theorem subd12_10_8 : subd12_10 [1] = true := by decide +kernel
theorem subd12_10_9 : subd12_10 [2] = true := by decide +kernel
theorem sbd12_10_0 : ∀ q ∈ blkd12_10_0, subd12_10 q = true := by
  unfold blkd12_10_0
  exact List.forall_mem_cons.2 ⟨subd12_10_0, List.forall_mem_cons.2 ⟨subd12_10_1, List.forall_mem_cons.2 ⟨subd12_10_2, List.forall_mem_cons.2 ⟨subd12_10_3, List.forall_mem_cons.2 ⟨subd12_10_4, List.forall_mem_cons.2 ⟨subd12_10_5, List.forall_mem_cons.2 ⟨subd12_10_6, List.forall_mem_cons.2 ⟨subd12_10_7, List.forall_mem_cons.2 ⟨subd12_10_8, List.forall_mem_cons.2 ⟨subd12_10_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd12_11 : ldCheck G d12_11.U d12_11.ms ldd12_11 = true := by decide +kernel
theorem pre_okd12_11 : subPre G cell12 d12_11 = true := by decide +kernel
theorem subd12_11_0 : subd12_11 [] = true := by decide +kernel
theorem sbd12_11_0 : ∀ q ∈ blkd12_11_0, subd12_11 q = true := by
  unfold blkd12_11_0
  exact List.forall_mem_cons.2 ⟨subd12_11_0, List.forall_mem_nil _⟩
theorem ld_okd13_0 : ldCheck G d13_0.U d13_0.ms ldd13_0 = true := by decide +kernel
theorem pre_okd13_0 : subPre G cell13 d13_0 = true := by decide +kernel
theorem subd13_0_0 : subd13_0 [] = true := by decide +kernel
theorem sbd13_0_0 : ∀ q ∈ blkd13_0_0, subd13_0 q = true := by
  unfold blkd13_0_0
  exact List.forall_mem_cons.2 ⟨subd13_0_0, List.forall_mem_nil _⟩
theorem ld_okd13_1 : ldCheck G d13_1.U d13_1.ms ldd13_1 = true := by decide +kernel
theorem pre_okd13_1 : subPre G cell13 d13_1 = true := by decide +kernel
theorem subd13_1_0 : subd13_1 [] = true := by decide +kernel
theorem sbd13_1_0 : ∀ q ∈ blkd13_1_0, subd13_1 q = true := by
  unfold blkd13_1_0
  exact List.forall_mem_cons.2 ⟨subd13_1_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C115
