import ReflectZphi.Data.Cert5.C132.Base

namespace ReflectZphi.Data.Cert5.C132

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
theorem subd17_2_0 : subd17_2 [-1] = true := by decide +kernel
theorem subd17_2_1 : subd17_2 [0] = true := by decide +kernel
theorem subd17_2_2 : subd17_2 [1] = true := by decide +kernel
theorem sbd17_2_0 : ∀ q ∈ blkd17_2_0, subd17_2 q = true := by
  unfold blkd17_2_0
  exact List.forall_mem_cons.2 ⟨subd17_2_0, List.forall_mem_cons.2 ⟨subd17_2_1, List.forall_mem_cons.2 ⟨subd17_2_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd17_3 : ldCheck G d17_3.U d17_3.ms ldd17_3 = true := by decide +kernel
theorem pre_okd17_3 : subPre G cell17 d17_3 = true := by decide +kernel
theorem subd17_3_0 : subd17_3 [-2] = true := by decide +kernel
theorem subd17_3_1 : subd17_3 [-1] = true := by decide +kernel
theorem subd17_3_2 : subd17_3 [0] = true := by decide +kernel
theorem subd17_3_3 : subd17_3 [1] = true := by decide +kernel
theorem subd17_3_4 : subd17_3 [2] = true := by decide +kernel
theorem sbd17_3_0 : ∀ q ∈ blkd17_3_0, subd17_3 q = true := by
  unfold blkd17_3_0
  exact List.forall_mem_cons.2 ⟨subd17_3_0, List.forall_mem_cons.2 ⟨subd17_3_1, List.forall_mem_cons.2 ⟨subd17_3_2, List.forall_mem_cons.2 ⟨subd17_3_3, List.forall_mem_cons.2 ⟨subd17_3_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd17_4 : ldCheck G d17_4.U d17_4.ms ldd17_4 = true := by decide +kernel
theorem pre_okd17_4 : subPre G cell17 d17_4 = true := by decide +kernel
theorem subd17_4_0 : subd17_4 [] = true := by decide +kernel
theorem sbd17_4_0 : ∀ q ∈ blkd17_4_0, subd17_4 q = true := by
  unfold blkd17_4_0
  exact List.forall_mem_cons.2 ⟨subd17_4_0, List.forall_mem_nil _⟩
theorem ld_okd17_5 : ldCheck G d17_5.U d17_5.ms ldd17_5 = true := by decide +kernel
theorem pre_okd17_5 : subPre G cell17 d17_5 = true := by decide +kernel
theorem subd17_5_0 : subd17_5 [] = true := by decide +kernel
theorem sbd17_5_0 : ∀ q ∈ blkd17_5_0, subd17_5 q = true := by
  unfold blkd17_5_0
  exact List.forall_mem_cons.2 ⟨subd17_5_0, List.forall_mem_nil _⟩
theorem ld_okd17_6 : ldCheck G d17_6.U d17_6.ms ldd17_6 = true := by decide +kernel
theorem pre_okd17_6 : subPre G cell17 d17_6 = true := by decide +kernel
theorem subd17_6_0 : subd17_6 [-1] = true := by decide +kernel
theorem subd17_6_1 : subd17_6 [0] = true := by decide +kernel
theorem subd17_6_2 : subd17_6 [1] = true := by decide +kernel
theorem sbd17_6_0 : ∀ q ∈ blkd17_6_0, subd17_6 q = true := by
  unfold blkd17_6_0
  exact List.forall_mem_cons.2 ⟨subd17_6_0, List.forall_mem_cons.2 ⟨subd17_6_1, List.forall_mem_cons.2 ⟨subd17_6_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd17_7 : ldCheck G d17_7.U d17_7.ms ldd17_7 = true := by decide +kernel
theorem pre_okd17_7 : subPre G cell17 d17_7 = true := by decide +kernel
theorem subd17_7_0 : subd17_7 [] = true := by decide +kernel
theorem sbd17_7_0 : ∀ q ∈ blkd17_7_0, subd17_7 q = true := by
  unfold blkd17_7_0
  exact List.forall_mem_cons.2 ⟨subd17_7_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C132
