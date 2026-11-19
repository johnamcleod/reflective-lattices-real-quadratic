import ReflectZphi.Data.Cert5.C129.Base

namespace ReflectZphi.Data.Cert5.C129

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd13_1_0 : subd13_1 [-2] = true := by decide +kernel
theorem subd13_1_1 : subd13_1 [-1] = true := by decide +kernel
theorem subd13_1_2 : subd13_1 [0] = true := by decide +kernel
theorem subd13_1_3 : subd13_1 [1] = true := by decide +kernel
theorem subd13_1_4 : subd13_1 [2] = true := by decide +kernel
theorem sbd13_1_0 : ∀ q ∈ blkd13_1_0, subd13_1 q = true := by
  unfold blkd13_1_0
  exact List.forall_mem_cons.2 ⟨subd13_1_0, List.forall_mem_cons.2 ⟨subd13_1_1, List.forall_mem_cons.2 ⟨subd13_1_2, List.forall_mem_cons.2 ⟨subd13_1_3, List.forall_mem_cons.2 ⟨subd13_1_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd13_2 : ldCheck G d13_2.U d13_2.ms ldd13_2 = true := by decide +kernel
theorem pre_okd13_2 : subPre G cell13 d13_2 = true := by decide +kernel
theorem subd13_2_0 : subd13_2 [-1] = true := by decide +kernel
theorem subd13_2_1 : subd13_2 [0, -2] = true := by decide +kernel
theorem subd13_2_2 : subd13_2 [0, -1] = true := by decide +kernel
theorem subd13_2_3 : subd13_2 [0, 0] = true := by decide +kernel
theorem subd13_2_4 : subd13_2 [0, 1] = true := by decide +kernel
theorem subd13_2_5 : subd13_2 [1] = true := by decide +kernel
theorem sbd13_2_0 : ∀ q ∈ blkd13_2_0, subd13_2 q = true := by
  unfold blkd13_2_0
  exact List.forall_mem_cons.2 ⟨subd13_2_0, List.forall_mem_cons.2 ⟨subd13_2_1, List.forall_mem_cons.2 ⟨subd13_2_2, List.forall_mem_cons.2 ⟨subd13_2_3, List.forall_mem_cons.2 ⟨subd13_2_4, List.forall_mem_cons.2 ⟨subd13_2_5, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem ld_okd13_3 : ldCheck G d13_3.U d13_3.ms ldd13_3 = true := by decide +kernel
theorem pre_okd13_3 : subPre G cell13 d13_3 = true := by decide +kernel
theorem subd13_3_0 : subd13_3 [-3] = true := by decide +kernel
theorem subd13_3_1 : subd13_3 [-2] = true := by decide +kernel
theorem subd13_3_2 : subd13_3 [-1] = true := by decide +kernel
theorem subd13_3_3 : subd13_3 [0] = true := by decide +kernel
theorem subd13_3_4 : subd13_3 [1] = true := by decide +kernel
theorem subd13_3_5 : subd13_3 [2] = true := by decide +kernel
theorem subd13_3_6 : subd13_3 [3] = true := by decide +kernel
theorem sbd13_3_0 : ∀ q ∈ blkd13_3_0, subd13_3 q = true := by
  unfold blkd13_3_0
  exact List.forall_mem_cons.2 ⟨subd13_3_0, List.forall_mem_cons.2 ⟨subd13_3_1, List.forall_mem_cons.2 ⟨subd13_3_2, List.forall_mem_cons.2 ⟨subd13_3_3, List.forall_mem_cons.2 ⟨subd13_3_4, List.forall_mem_cons.2 ⟨subd13_3_5, List.forall_mem_cons.2 ⟨subd13_3_6, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C129
