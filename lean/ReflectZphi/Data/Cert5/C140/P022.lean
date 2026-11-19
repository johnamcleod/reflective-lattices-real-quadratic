import ReflectZphi.Data.Cert5.C140.Base

namespace ReflectZphi.Data.Cert5.C140

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd17_0 : ldCheck G d17_0.U d17_0.ms ldd17_0 = true := by decide +kernel
theorem pre_okd17_0 : subPre G cell17 d17_0 = true := by decide +kernel
theorem subd17_0_0 : subd17_0 [] = true := by decide +kernel
theorem sbd17_0_0 : ∀ q ∈ blkd17_0_0, subd17_0 q = true := by
  unfold blkd17_0_0
  exact List.forall_mem_cons.2 ⟨subd17_0_0, List.forall_mem_nil _⟩
theorem ld_okd17_1 : ldCheck G d17_1.U d17_1.ms ldd17_1 = true := by decide +kernel
theorem pre_okd17_1 : subPre G cell17 d17_1 = true := by decide +kernel
theorem subd17_1_0 : subd17_1 [] = true := by decide +kernel
theorem sbd17_1_0 : ∀ q ∈ blkd17_1_0, subd17_1 q = true := by
  unfold blkd17_1_0
  exact List.forall_mem_cons.2 ⟨subd17_1_0, List.forall_mem_nil _⟩
theorem ld_okd17_2 : ldCheck G d17_2.U d17_2.ms ldd17_2 = true := by decide +kernel
theorem pre_okd17_2 : subPre G cell17 d17_2 = true := by decide +kernel
theorem subd17_2_0 : subd17_2 [] = true := by decide +kernel
theorem sbd17_2_0 : ∀ q ∈ blkd17_2_0, subd17_2 q = true := by
  unfold blkd17_2_0
  exact List.forall_mem_cons.2 ⟨subd17_2_0, List.forall_mem_nil _⟩
theorem ld_okd17_3 : ldCheck G d17_3.U d17_3.ms ldd17_3 = true := by decide +kernel
theorem pre_okd17_3 : subPre G cell17 d17_3 = true := by decide +kernel
theorem subd17_3_0 : subd17_3 [-3] = true := by decide +kernel
theorem subd17_3_1 : subd17_3 [-2] = true := by decide +kernel
theorem subd17_3_2 : subd17_3 [-1] = true := by decide +kernel
theorem subd17_3_3 : subd17_3 [0] = true := by decide +kernel
theorem subd17_3_4 : subd17_3 [1] = true := by decide +kernel
theorem subd17_3_5 : subd17_3 [2] = true := by decide +kernel
theorem subd17_3_6 : subd17_3 [3] = true := by decide +kernel
theorem sbd17_3_0 : ∀ q ∈ blkd17_3_0, subd17_3 q = true := by
  unfold blkd17_3_0
  exact List.forall_mem_cons.2 ⟨subd17_3_0, List.forall_mem_cons.2 ⟨subd17_3_1, List.forall_mem_cons.2 ⟨subd17_3_2, List.forall_mem_cons.2 ⟨subd17_3_3, List.forall_mem_cons.2 ⟨subd17_3_4, List.forall_mem_cons.2 ⟨subd17_3_5, List.forall_mem_cons.2 ⟨subd17_3_6, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd17_4 : ldCheck G d17_4.U d17_4.ms ldd17_4 = true := by decide +kernel
theorem pre_okd17_4 : subPre G cell17 d17_4 = true := by decide +kernel
theorem subd17_4_0 : subd17_4 [-2] = true := by decide +kernel
theorem subd17_4_1 : subd17_4 [-1] = true := by decide +kernel
theorem subd17_4_2 : subd17_4 [0] = true := by decide +kernel
theorem subd17_4_3 : subd17_4 [1] = true := by decide +kernel
theorem subd17_4_4 : subd17_4 [2] = true := by decide +kernel
theorem sbd17_4_0 : ∀ q ∈ blkd17_4_0, subd17_4 q = true := by
  unfold blkd17_4_0
  exact List.forall_mem_cons.2 ⟨subd17_4_0, List.forall_mem_cons.2 ⟨subd17_4_1, List.forall_mem_cons.2 ⟨subd17_4_2, List.forall_mem_cons.2 ⟨subd17_4_3, List.forall_mem_cons.2 ⟨subd17_4_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd17_5 : ldCheck G d17_5.U d17_5.ms ldd17_5 = true := by decide +kernel
theorem pre_okd17_5 : subPre G cell17 d17_5 = true := by decide +kernel
theorem subd17_5_0 : subd17_5 [] = true := by decide +kernel
theorem sbd17_5_0 : ∀ q ∈ blkd17_5_0, subd17_5 q = true := by
  unfold blkd17_5_0
  exact List.forall_mem_cons.2 ⟨subd17_5_0, List.forall_mem_nil _⟩
theorem ld_okd18_0 : ldCheck G d18_0.U d18_0.ms ldd18_0 = true := by decide +kernel
theorem pre_okd18_0 : subPre G cell18 d18_0 = true := by decide +kernel
theorem subd18_0_0 : subd18_0 [] = true := by decide +kernel
theorem sbd18_0_0 : ∀ q ∈ blkd18_0_0, subd18_0 q = true := by
  unfold blkd18_0_0
  exact List.forall_mem_cons.2 ⟨subd18_0_0, List.forall_mem_nil _⟩
theorem ld_okd18_1 : ldCheck G d18_1.U d18_1.ms ldd18_1 = true := by decide +kernel
theorem pre_okd18_1 : subPre G cell18 d18_1 = true := by decide +kernel
theorem subd18_1_0 : subd18_1 [] = true := by decide +kernel
theorem sbd18_1_0 : ∀ q ∈ blkd18_1_0, subd18_1 q = true := by
  unfold blkd18_1_0
  exact List.forall_mem_cons.2 ⟨subd18_1_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C140
