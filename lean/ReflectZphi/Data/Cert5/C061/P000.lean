import ReflectZphi.Data.Cert5.C061.Base

namespace ReflectZphi.Data.Cert5.C061

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd0_0 : ldCheck G d0_0.U d0_0.ms ldd0_0 = true := by decide +kernel
theorem pre_okd0_0 : subPre G cell0 d0_0 = true := by decide +kernel
theorem subd0_0_0 : subd0_0 [-2] = true := by decide +kernel
theorem subd0_0_1 : subd0_0 [-1] = true := by decide +kernel
theorem subd0_0_2 : subd0_0 [0] = true := by decide +kernel
theorem subd0_0_3 : subd0_0 [1] = true := by decide +kernel
theorem subd0_0_4 : subd0_0 [2] = true := by decide +kernel
theorem sbd0_0_0 : ∀ q ∈ blkd0_0_0, subd0_0 q = true := by
  unfold blkd0_0_0
  exact List.forall_mem_cons.2 ⟨subd0_0_0, List.forall_mem_cons.2 ⟨subd0_0_1, List.forall_mem_cons.2 ⟨subd0_0_2, List.forall_mem_cons.2 ⟨subd0_0_3, List.forall_mem_cons.2 ⟨subd0_0_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd0_1 : ldCheck G d0_1.U d0_1.ms ldd0_1 = true := by decide +kernel
theorem pre_okd0_1 : subPre G cell0 d0_1 = true := by decide +kernel
theorem subd0_1_0 : subd0_1 [-2] = true := by decide +kernel
theorem subd0_1_1 : subd0_1 [-1] = true := by decide +kernel
theorem subd0_1_2 : subd0_1 [0] = true := by decide +kernel
theorem subd0_1_3 : subd0_1 [1] = true := by decide +kernel
theorem subd0_1_4 : subd0_1 [2] = true := by decide +kernel
theorem sbd0_1_0 : ∀ q ∈ blkd0_1_0, subd0_1 q = true := by
  unfold blkd0_1_0
  exact List.forall_mem_cons.2 ⟨subd0_1_0, List.forall_mem_cons.2 ⟨subd0_1_1, List.forall_mem_cons.2 ⟨subd0_1_2, List.forall_mem_cons.2 ⟨subd0_1_3, List.forall_mem_cons.2 ⟨subd0_1_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd0_2 : ldCheck G d0_2.U d0_2.ms ldd0_2 = true := by decide +kernel
theorem pre_okd0_2 : subPre G cell0 d0_2 = true := by decide +kernel
theorem subd0_2_0 : subd0_2 [] = true := by decide +kernel
theorem sbd0_2_0 : ∀ q ∈ blkd0_2_0, subd0_2 q = true := by
  unfold blkd0_2_0
  exact List.forall_mem_cons.2 ⟨subd0_2_0, List.forall_mem_nil _⟩
theorem ld_okd0_3 : ldCheck G d0_3.U d0_3.ms ldd0_3 = true := by decide +kernel
theorem pre_okd0_3 : subPre G cell0 d0_3 = true := by decide +kernel
theorem subd0_3_0 : subd0_3 [] = true := by decide +kernel
theorem sbd0_3_0 : ∀ q ∈ blkd0_3_0, subd0_3 q = true := by
  unfold blkd0_3_0
  exact List.forall_mem_cons.2 ⟨subd0_3_0, List.forall_mem_nil _⟩
theorem ld_okd1_0 : ldCheck G d1_0.U d1_0.ms ldd1_0 = true := by decide +kernel
theorem pre_okd1_0 : subPre G cell1 d1_0 = true := by decide +kernel
theorem subd1_0_0 : subd1_0 [-2] = true := by decide +kernel
theorem subd1_0_1 : subd1_0 [-1] = true := by decide +kernel
theorem subd1_0_2 : subd1_0 [0] = true := by decide +kernel
theorem subd1_0_3 : subd1_0 [1] = true := by decide +kernel
theorem subd1_0_4 : subd1_0 [2] = true := by decide +kernel
theorem sbd1_0_0 : ∀ q ∈ blkd1_0_0, subd1_0 q = true := by
  unfold blkd1_0_0
  exact List.forall_mem_cons.2 ⟨subd1_0_0, List.forall_mem_cons.2 ⟨subd1_0_1, List.forall_mem_cons.2 ⟨subd1_0_2, List.forall_mem_cons.2 ⟨subd1_0_3, List.forall_mem_cons.2 ⟨subd1_0_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd1_1 : ldCheck G d1_1.U d1_1.ms ldd1_1 = true := by decide +kernel
theorem pre_okd1_1 : subPre G cell1 d1_1 = true := by decide +kernel
theorem subd1_1_0 : subd1_1 [-1] = true := by decide +kernel
theorem subd1_1_1 : subd1_1 [0] = true := by decide +kernel
theorem subd1_1_2 : subd1_1 [1] = true := by decide +kernel
theorem sbd1_1_0 : ∀ q ∈ blkd1_1_0, subd1_1 q = true := by
  unfold blkd1_1_0
  exact List.forall_mem_cons.2 ⟨subd1_1_0, List.forall_mem_cons.2 ⟨subd1_1_1, List.forall_mem_cons.2 ⟨subd1_1_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd1_2 : ldCheck G d1_2.U d1_2.ms ldd1_2 = true := by decide +kernel
theorem pre_okd1_2 : subPre G cell1 d1_2 = true := by decide +kernel
theorem subd1_2_0 : subd1_2 [] = true := by decide +kernel
theorem sbd1_2_0 : ∀ q ∈ blkd1_2_0, subd1_2 q = true := by
  unfold blkd1_2_0
  exact List.forall_mem_cons.2 ⟨subd1_2_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C061
