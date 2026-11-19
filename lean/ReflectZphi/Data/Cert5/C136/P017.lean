import ReflectZphi.Data.Cert5.C136.Base

namespace ReflectZphi.Data.Cert5.C136

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd12_1_0 : subd12_1 [-2] = true := by decide +kernel
theorem subd12_1_1 : subd12_1 [-1] = true := by decide +kernel
theorem subd12_1_2 : subd12_1 [0, -3] = true := by decide +kernel
theorem subd12_1_3 : subd12_1 [0, -2] = true := by decide +kernel
theorem subd12_1_4 : subd12_1 [0, -1] = true := by decide +kernel
theorem subd12_1_5 : subd12_1 [0, 0] = true := by decide +kernel
theorem subd12_1_6 : subd12_1 [0, 1] = true := by decide +kernel
theorem subd12_1_7 : subd12_1 [0, 2] = true := by decide +kernel
theorem subd12_1_8 : subd12_1 [1] = true := by decide +kernel
theorem subd12_1_9 : subd12_1 [2] = true := by decide +kernel
theorem sbd12_1_0 : ∀ q ∈ blkd12_1_0, subd12_1 q = true := by
  unfold blkd12_1_0
  exact List.forall_mem_cons.2 ⟨subd12_1_0, List.forall_mem_cons.2 ⟨subd12_1_1, List.forall_mem_cons.2 ⟨subd12_1_2, List.forall_mem_cons.2 ⟨subd12_1_3, List.forall_mem_cons.2 ⟨subd12_1_4, List.forall_mem_cons.2 ⟨subd12_1_5, List.forall_mem_cons.2 ⟨subd12_1_6, List.forall_mem_cons.2 ⟨subd12_1_7, List.forall_mem_cons.2 ⟨subd12_1_8, List.forall_mem_cons.2 ⟨subd12_1_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd12_2 : ldCheck G d12_2.U d12_2.ms ldd12_2 = true := by decide +kernel
theorem pre_okd12_2 : subPre G cell12 d12_2 = true := by decide +kernel
theorem subd12_2_0 : subd12_2 [-1] = true := by decide +kernel
theorem subd12_2_1 : subd12_2 [0] = true := by decide +kernel
theorem subd12_2_2 : subd12_2 [1] = true := by decide +kernel
theorem sbd12_2_0 : ∀ q ∈ blkd12_2_0, subd12_2 q = true := by
  unfold blkd12_2_0
  exact List.forall_mem_cons.2 ⟨subd12_2_0, List.forall_mem_cons.2 ⟨subd12_2_1, List.forall_mem_cons.2 ⟨subd12_2_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd12_3 : ldCheck G d12_3.U d12_3.ms ldd12_3 = true := by decide +kernel
theorem pre_okd12_3 : subPre G cell12 d12_3 = true := by decide +kernel
theorem subd12_3_0 : subd12_3 [-2] = true := by decide +kernel
theorem subd12_3_1 : subd12_3 [-1] = true := by decide +kernel
theorem subd12_3_2 : subd12_3 [0] = true := by decide +kernel
theorem subd12_3_3 : subd12_3 [1] = true := by decide +kernel
theorem subd12_3_4 : subd12_3 [2] = true := by decide +kernel
theorem sbd12_3_0 : ∀ q ∈ blkd12_3_0, subd12_3 q = true := by
  unfold blkd12_3_0
  exact List.forall_mem_cons.2 ⟨subd12_3_0, List.forall_mem_cons.2 ⟨subd12_3_1, List.forall_mem_cons.2 ⟨subd12_3_2, List.forall_mem_cons.2 ⟨subd12_3_3, List.forall_mem_cons.2 ⟨subd12_3_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
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
theorem ld_okd13_2 : ldCheck G d13_2.U d13_2.ms ldd13_2 = true := by decide +kernel
theorem pre_okd13_2 : subPre G cell13 d13_2 = true := by decide +kernel
theorem subd13_2_0 : subd13_2 [] = true := by decide +kernel
theorem sbd13_2_0 : ∀ q ∈ blkd13_2_0, subd13_2 q = true := by
  unfold blkd13_2_0
  exact List.forall_mem_cons.2 ⟨subd13_2_0, List.forall_mem_nil _⟩
theorem ld_okd13_3 : ldCheck G d13_3.U d13_3.ms ldd13_3 = true := by decide +kernel
theorem pre_okd13_3 : subPre G cell13 d13_3 = true := by decide +kernel
theorem subd13_3_0 : subd13_3 [] = true := by decide +kernel
theorem sbd13_3_0 : ∀ q ∈ blkd13_3_0, subd13_3 q = true := by
  unfold blkd13_3_0
  exact List.forall_mem_cons.2 ⟨subd13_3_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C136
