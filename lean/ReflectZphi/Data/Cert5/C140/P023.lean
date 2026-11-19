import ReflectZphi.Data.Cert5.C140.Base

namespace ReflectZphi.Data.Cert5.C140

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd18_2 : ldCheck G d18_2.U d18_2.ms ldd18_2 = true := by decide +kernel
theorem pre_okd18_2 : subPre G cell18 d18_2 = true := by decide +kernel
theorem subd18_2_0 : subd18_2 [] = true := by decide +kernel
theorem sbd18_2_0 : ∀ q ∈ blkd18_2_0, subd18_2 q = true := by
  unfold blkd18_2_0
  exact List.forall_mem_cons.2 ⟨subd18_2_0, List.forall_mem_nil _⟩
theorem ld_okd18_3 : ldCheck G d18_3.U d18_3.ms ldd18_3 = true := by decide +kernel
theorem pre_okd18_3 : subPre G cell18 d18_3 = true := by decide +kernel
theorem subd18_3_0 : subd18_3 [-1] = true := by decide +kernel
theorem subd18_3_1 : subd18_3 [0, -3] = true := by decide +kernel
theorem subd18_3_2 : subd18_3 [0, -2] = true := by decide +kernel
theorem subd18_3_3 : subd18_3 [0, -1] = true := by decide +kernel
theorem subd18_3_4 : subd18_3 [0, 0] = true := by decide +kernel
theorem subd18_3_5 : subd18_3 [0, 1] = true := by decide +kernel
theorem subd18_3_6 : subd18_3 [0, 2] = true := by decide +kernel
theorem subd18_3_7 : subd18_3 [1] = true := by decide +kernel
theorem sbd18_3_0 : ∀ q ∈ blkd18_3_0, subd18_3 q = true := by
  unfold blkd18_3_0
  exact List.forall_mem_cons.2 ⟨subd18_3_0, List.forall_mem_cons.2 ⟨subd18_3_1, List.forall_mem_cons.2 ⟨subd18_3_2, List.forall_mem_cons.2 ⟨subd18_3_3, List.forall_mem_cons.2 ⟨subd18_3_4, List.forall_mem_cons.2 ⟨subd18_3_5, List.forall_mem_cons.2 ⟨subd18_3_6, List.forall_mem_cons.2 ⟨subd18_3_7, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd18_4 : ldCheck G d18_4.U d18_4.ms ldd18_4 = true := by decide +kernel
theorem pre_okd18_4 : subPre G cell18 d18_4 = true := by decide +kernel
theorem subd18_4_0 : subd18_4 [-2] = true := by decide +kernel
theorem subd18_4_1 : subd18_4 [-1] = true := by decide +kernel
theorem subd18_4_2 : subd18_4 [0] = true := by decide +kernel
theorem subd18_4_3 : subd18_4 [1] = true := by decide +kernel
theorem subd18_4_4 : subd18_4 [2] = true := by decide +kernel
theorem sbd18_4_0 : ∀ q ∈ blkd18_4_0, subd18_4 q = true := by
  unfold blkd18_4_0
  exact List.forall_mem_cons.2 ⟨subd18_4_0, List.forall_mem_cons.2 ⟨subd18_4_1, List.forall_mem_cons.2 ⟨subd18_4_2, List.forall_mem_cons.2 ⟨subd18_4_3, List.forall_mem_cons.2 ⟨subd18_4_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd18_5 : ldCheck G d18_5.U d18_5.ms ldd18_5 = true := by decide +kernel
theorem pre_okd18_5 : subPre G cell18 d18_5 = true := by decide +kernel
theorem subd18_5_0 : subd18_5 [] = true := by decide +kernel
theorem sbd18_5_0 : ∀ q ∈ blkd18_5_0, subd18_5 q = true := by
  unfold blkd18_5_0
  exact List.forall_mem_cons.2 ⟨subd18_5_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C140
