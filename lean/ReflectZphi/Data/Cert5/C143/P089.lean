import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd32_1 : ldCheck G d32_1.U d32_1.ms ldd32_1 = true := by decide +kernel
theorem pre_okd32_1 : subPre G cell32 d32_1 = true := by decide +kernel
theorem subd32_1_0 : subd32_1 [-2] = true := by decide +kernel
theorem subd32_1_1 : subd32_1 [-1] = true := by decide +kernel
theorem subd32_1_2 : subd32_1 [0] = true := by decide +kernel
theorem subd32_1_3 : subd32_1 [1] = true := by decide +kernel
theorem subd32_1_4 : subd32_1 [2] = true := by decide +kernel
theorem sbd32_1_0 : ∀ q ∈ blkd32_1_0, subd32_1 q = true := by
  unfold blkd32_1_0
  exact List.forall_mem_cons.2 ⟨subd32_1_0, List.forall_mem_cons.2 ⟨subd32_1_1, List.forall_mem_cons.2 ⟨subd32_1_2, List.forall_mem_cons.2 ⟨subd32_1_3, List.forall_mem_cons.2 ⟨subd32_1_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd32_2 : ldCheck G d32_2.U d32_2.ms ldd32_2 = true := by decide +kernel
theorem pre_okd32_2 : subPre G cell32 d32_2 = true := by decide +kernel
theorem subd32_2_0 : subd32_2 [-2] = true := by decide +kernel
theorem subd32_2_1 : subd32_2 [-1] = true := by decide +kernel
theorem subd32_2_2 : subd32_2 [0] = true := by decide +kernel
theorem subd32_2_3 : subd32_2 [1] = true := by decide +kernel
theorem subd32_2_4 : subd32_2 [2] = true := by decide +kernel
theorem sbd32_2_0 : ∀ q ∈ blkd32_2_0, subd32_2 q = true := by
  unfold blkd32_2_0
  exact List.forall_mem_cons.2 ⟨subd32_2_0, List.forall_mem_cons.2 ⟨subd32_2_1, List.forall_mem_cons.2 ⟨subd32_2_2, List.forall_mem_cons.2 ⟨subd32_2_3, List.forall_mem_cons.2 ⟨subd32_2_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd32_3 : ldCheck G d32_3.U d32_3.ms ldd32_3 = true := by decide +kernel
theorem pre_okd32_3 : subPre G cell32 d32_3 = true := by decide +kernel
theorem subd32_3_0 : subd32_3 [-2] = true := by decide +kernel
theorem subd32_3_1 : subd32_3 [-1] = true := by decide +kernel
theorem subd32_3_2 : subd32_3 [0] = true := by decide +kernel
theorem subd32_3_3 : subd32_3 [1] = true := by decide +kernel
theorem subd32_3_4 : subd32_3 [2] = true := by decide +kernel
theorem sbd32_3_0 : ∀ q ∈ blkd32_3_0, subd32_3 q = true := by
  unfold blkd32_3_0
  exact List.forall_mem_cons.2 ⟨subd32_3_0, List.forall_mem_cons.2 ⟨subd32_3_1, List.forall_mem_cons.2 ⟨subd32_3_2, List.forall_mem_cons.2 ⟨subd32_3_3, List.forall_mem_cons.2 ⟨subd32_3_4, List.forall_mem_nil _⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
