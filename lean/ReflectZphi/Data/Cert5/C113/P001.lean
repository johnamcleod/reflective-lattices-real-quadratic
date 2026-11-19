import ReflectZphi.Data.Cert5.C113.Base

namespace ReflectZphi.Data.Cert5.C113

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd0_8 : ldCheck G d0_8.U d0_8.ms ldd0_8 = true := by decide +kernel
theorem pre_okd0_8 : subPre G cell0 d0_8 = true := by decide +kernel
theorem subd0_8_0 : subd0_8 [-2] = true := by decide +kernel
theorem subd0_8_1 : subd0_8 [-1] = true := by decide +kernel
theorem subd0_8_2 : subd0_8 [0, -3] = true := by decide +kernel
theorem subd0_8_3 : subd0_8 [0, -2] = true := by decide +kernel
theorem subd0_8_4 : subd0_8 [0, -1] = true := by decide +kernel
theorem subd0_8_5 : subd0_8 [0, 0] = true := by decide +kernel
theorem subd0_8_6 : subd0_8 [0, 1] = true := by decide +kernel
theorem subd0_8_7 : subd0_8 [0, 2] = true := by decide +kernel
theorem subd0_8_8 : subd0_8 [1] = true := by decide +kernel
theorem subd0_8_9 : subd0_8 [2] = true := by decide +kernel
theorem sbd0_8_0 : ∀ q ∈ blkd0_8_0, subd0_8 q = true := by
  unfold blkd0_8_0
  exact List.forall_mem_cons.2 ⟨subd0_8_0, List.forall_mem_cons.2 ⟨subd0_8_1, List.forall_mem_cons.2 ⟨subd0_8_2, List.forall_mem_cons.2 ⟨subd0_8_3, List.forall_mem_cons.2 ⟨subd0_8_4, List.forall_mem_cons.2 ⟨subd0_8_5, List.forall_mem_cons.2 ⟨subd0_8_6, List.forall_mem_cons.2 ⟨subd0_8_7, List.forall_mem_cons.2 ⟨subd0_8_8, List.forall_mem_cons.2 ⟨subd0_8_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd0_9 : ldCheck G d0_9.U d0_9.ms ldd0_9 = true := by decide +kernel
theorem pre_okd0_9 : subPre G cell0 d0_9 = true := by decide +kernel
theorem subd0_9_0 : subd0_9 [] = true := by decide +kernel
theorem sbd0_9_0 : ∀ q ∈ blkd0_9_0, subd0_9 q = true := by
  unfold blkd0_9_0
  exact List.forall_mem_cons.2 ⟨subd0_9_0, List.forall_mem_nil _⟩
theorem ld_okd1_0 : ldCheck G d1_0.U d1_0.ms ldd1_0 = true := by decide +kernel
theorem pre_okd1_0 : subPre G cell1 d1_0 = true := by decide +kernel
theorem subd1_0_0 : subd1_0 [] = true := by decide +kernel
theorem sbd1_0_0 : ∀ q ∈ blkd1_0_0, subd1_0 q = true := by
  unfold blkd1_0_0
  exact List.forall_mem_cons.2 ⟨subd1_0_0, List.forall_mem_nil _⟩
theorem ld_okd1_1 : ldCheck G d1_1.U d1_1.ms ldd1_1 = true := by decide +kernel
theorem pre_okd1_1 : subPre G cell1 d1_1 = true := by decide +kernel
theorem subd1_1_0 : subd1_1 [] = true := by decide +kernel
theorem sbd1_1_0 : ∀ q ∈ blkd1_1_0, subd1_1 q = true := by
  unfold blkd1_1_0
  exact List.forall_mem_cons.2 ⟨subd1_1_0, List.forall_mem_nil _⟩
theorem ld_okd1_2 : ldCheck G d1_2.U d1_2.ms ldd1_2 = true := by decide +kernel
theorem pre_okd1_2 : subPre G cell1 d1_2 = true := by decide +kernel
theorem subd1_2_0 : subd1_2 [] = true := by decide +kernel
theorem sbd1_2_0 : ∀ q ∈ blkd1_2_0, subd1_2 q = true := by
  unfold blkd1_2_0
  exact List.forall_mem_cons.2 ⟨subd1_2_0, List.forall_mem_nil _⟩
theorem ld_okd1_3 : ldCheck G d1_3.U d1_3.ms ldd1_3 = true := by decide +kernel
theorem pre_okd1_3 : subPre G cell1 d1_3 = true := by decide +kernel
theorem subd1_3_0 : subd1_3 [] = true := by decide +kernel
theorem sbd1_3_0 : ∀ q ∈ blkd1_3_0, subd1_3 q = true := by
  unfold blkd1_3_0
  exact List.forall_mem_cons.2 ⟨subd1_3_0, List.forall_mem_nil _⟩
theorem ld_okd1_4 : ldCheck G d1_4.U d1_4.ms ldd1_4 = true := by decide +kernel
theorem pre_okd1_4 : subPre G cell1 d1_4 = true := by decide +kernel
theorem subd1_4_0 : subd1_4 [] = true := by decide +kernel
theorem sbd1_4_0 : ∀ q ∈ blkd1_4_0, subd1_4 q = true := by
  unfold blkd1_4_0
  exact List.forall_mem_cons.2 ⟨subd1_4_0, List.forall_mem_nil _⟩
theorem ld_okd1_5 : ldCheck G d1_5.U d1_5.ms ldd1_5 = true := by decide +kernel
theorem pre_okd1_5 : subPre G cell1 d1_5 = true := by decide +kernel
theorem subd1_5_0 : subd1_5 [] = true := by decide +kernel
theorem sbd1_5_0 : ∀ q ∈ blkd1_5_0, subd1_5 q = true := by
  unfold blkd1_5_0
  exact List.forall_mem_cons.2 ⟨subd1_5_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C113
