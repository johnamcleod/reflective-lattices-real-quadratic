import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd12_7_0 : subd12_7 [-1] = true := by decide +kernel
theorem subd12_7_1 : subd12_7 [0] = true := by decide +kernel
theorem subd12_7_2 : subd12_7 [1] = true := by decide +kernel
theorem sbd12_7_0 : ∀ q ∈ blkd12_7_0, subd12_7 q = true := by
  unfold blkd12_7_0
  exact List.forall_mem_cons.2 ⟨subd12_7_0, List.forall_mem_cons.2 ⟨subd12_7_1, List.forall_mem_cons.2 ⟨subd12_7_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd12_8 : ldCheck G d12_8.U d12_8.ms ldd12_8 = true := by decide +kernel
theorem pre_okd12_8 : subPre G cell12 d12_8 = true := by decide +kernel
theorem subd12_8_0 : subd12_8 [-1, -2] = true := by decide +kernel
theorem subd12_8_1 : subd12_8 [-1, -1] = true := by decide +kernel
theorem subd12_8_2 : subd12_8 [-1, 0] = true := by decide +kernel
theorem subd12_8_3 : subd12_8 [-1, 1] = true := by decide +kernel
theorem subd12_8_4 : subd12_8 [0, -2] = true := by decide +kernel
theorem subd12_8_5 : subd12_8 [0, -1] = true := by decide +kernel
theorem subd12_8_6 : subd12_8 [0, 0] = true := by decide +kernel
theorem subd12_8_7 : subd12_8 [0, 1] = true := by decide +kernel
theorem subd12_8_8 : subd12_8 [1, -2] = true := by decide +kernel
theorem subd12_8_9 : subd12_8 [1, -1] = true := by decide +kernel
theorem subd12_8_10 : subd12_8 [1, 0] = true := by decide +kernel
theorem subd12_8_11 : subd12_8 [1, 1] = true := by decide +kernel
theorem sbd12_8_0 : ∀ q ∈ blkd12_8_0, subd12_8 q = true := by
  unfold blkd12_8_0
  exact List.forall_mem_cons.2 ⟨subd12_8_0, List.forall_mem_cons.2 ⟨subd12_8_1, List.forall_mem_cons.2 ⟨subd12_8_2, List.forall_mem_cons.2 ⟨subd12_8_3, List.forall_mem_cons.2 ⟨subd12_8_4, List.forall_mem_cons.2 ⟨subd12_8_5, List.forall_mem_cons.2 ⟨subd12_8_6, List.forall_mem_cons.2 ⟨subd12_8_7, List.forall_mem_cons.2 ⟨subd12_8_8, List.forall_mem_cons.2 ⟨subd12_8_9, List.forall_mem_cons.2 ⟨subd12_8_10, List.forall_mem_cons.2 ⟨subd12_8_11, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd12_9 : ldCheck G d12_9.U d12_9.ms ldd12_9 = true := by decide +kernel
theorem pre_okd12_9 : subPre G cell12 d12_9 = true := by decide +kernel
theorem subd12_9_0 : subd12_9 [-2] = true := by decide +kernel
theorem subd12_9_1 : subd12_9 [-1] = true := by decide +kernel
theorem subd12_9_2 : subd12_9 [0] = true := by decide +kernel
theorem subd12_9_3 : subd12_9 [1] = true := by decide +kernel
theorem subd12_9_4 : subd12_9 [2] = true := by decide +kernel
theorem sbd12_9_0 : ∀ q ∈ blkd12_9_0, subd12_9 q = true := by
  unfold blkd12_9_0
  exact List.forall_mem_cons.2 ⟨subd12_9_0, List.forall_mem_cons.2 ⟨subd12_9_1, List.forall_mem_cons.2 ⟨subd12_9_2, List.forall_mem_cons.2 ⟨subd12_9_3, List.forall_mem_cons.2 ⟨subd12_9_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd12_10 : ldCheck G d12_10.U d12_10.ms ldd12_10 = true := by decide +kernel
theorem pre_okd12_10 : subPre G cell12 d12_10 = true := by decide +kernel
theorem subd12_10_0 : subd12_10 [-2] = true := by decide +kernel
theorem subd12_10_1 : subd12_10 [-1] = true := by decide +kernel
theorem subd12_10_2 : subd12_10 [0] = true := by decide +kernel
theorem subd12_10_3 : subd12_10 [1] = true := by decide +kernel
theorem subd12_10_4 : subd12_10 [2] = true := by decide +kernel
theorem sbd12_10_0 : ∀ q ∈ blkd12_10_0, subd12_10 q = true := by
  unfold blkd12_10_0
  exact List.forall_mem_cons.2 ⟨subd12_10_0, List.forall_mem_cons.2 ⟨subd12_10_1, List.forall_mem_cons.2 ⟨subd12_10_2, List.forall_mem_cons.2 ⟨subd12_10_3, List.forall_mem_cons.2 ⟨subd12_10_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd12_11 : ldCheck G d12_11.U d12_11.ms ldd12_11 = true := by decide +kernel
theorem pre_okd12_11 : subPre G cell12 d12_11 = true := by decide +kernel
theorem subd12_11_0 : subd12_11 [-2] = true := by decide +kernel
theorem subd12_11_1 : subd12_11 [-1] = true := by decide +kernel
theorem subd12_11_2 : subd12_11 [0] = true := by decide +kernel
theorem subd12_11_3 : subd12_11 [1] = true := by decide +kernel
theorem subd12_11_4 : subd12_11 [2] = true := by decide +kernel
theorem sbd12_11_0 : ∀ q ∈ blkd12_11_0, subd12_11 q = true := by
  unfold blkd12_11_0
  exact List.forall_mem_cons.2 ⟨subd12_11_0, List.forall_mem_cons.2 ⟨subd12_11_1, List.forall_mem_cons.2 ⟨subd12_11_2, List.forall_mem_cons.2 ⟨subd12_11_3, List.forall_mem_cons.2 ⟨subd12_11_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd12_12 : ldCheck G d12_12.U d12_12.ms ldd12_12 = true := by decide +kernel
theorem pre_okd12_12 : subPre G cell12 d12_12 = true := by decide +kernel
theorem subd12_12_0 : subd12_12 [] = true := by decide +kernel
theorem sbd12_12_0 : ∀ q ∈ blkd12_12_0, subd12_12 q = true := by
  unfold blkd12_12_0
  exact List.forall_mem_cons.2 ⟨subd12_12_0, List.forall_mem_nil _⟩
theorem ld_okd12_13 : ldCheck G d12_13.U d12_13.ms ldd12_13 = true := by decide +kernel
theorem pre_okd12_13 : subPre G cell12 d12_13 = true := by decide +kernel
theorem subd12_13_0 : subd12_13 [] = true := by decide +kernel
theorem sbd12_13_0 : ∀ q ∈ blkd12_13_0, subd12_13 q = true := by
  unfold blkd12_13_0
  exact List.forall_mem_cons.2 ⟨subd12_13_0, List.forall_mem_nil _⟩
theorem ld_okd12_14 : ldCheck G d12_14.U d12_14.ms ldd12_14 = true := by decide +kernel
theorem pre_okd12_14 : subPre G cell12 d12_14 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C124
