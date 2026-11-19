import ReflectZphi.Data.Cert5.C065.Base

namespace ReflectZphi.Data.Cert5.C065

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd0_9 : ldCheck G d0_9.U d0_9.ms ldd0_9 = true := by decide +kernel
theorem pre_okd0_9 : subPre G cell0 d0_9 = true := by decide +kernel
theorem subd0_9_0 : subd0_9 [] = true := by decide +kernel
theorem sbd0_9_0 : ∀ q ∈ blkd0_9_0, subd0_9 q = true := by
  unfold blkd0_9_0
  exact List.forall_mem_cons.2 ⟨subd0_9_0, List.forall_mem_nil _⟩
theorem ld_okd0_10 : ldCheck G d0_10.U d0_10.ms ldd0_10 = true := by decide +kernel
theorem pre_okd0_10 : subPre G cell0 d0_10 = true := by decide +kernel
theorem subd0_10_0 : subd0_10 [] = true := by decide +kernel
theorem sbd0_10_0 : ∀ q ∈ blkd0_10_0, subd0_10 q = true := by
  unfold blkd0_10_0
  exact List.forall_mem_cons.2 ⟨subd0_10_0, List.forall_mem_nil _⟩
theorem ld_okd0_11 : ldCheck G d0_11.U d0_11.ms ldd0_11 = true := by decide +kernel
theorem pre_okd0_11 : subPre G cell0 d0_11 = true := by decide +kernel
theorem subd0_11_0 : subd0_11 [] = true := by decide +kernel
theorem sbd0_11_0 : ∀ q ∈ blkd0_11_0, subd0_11 q = true := by
  unfold blkd0_11_0
  exact List.forall_mem_cons.2 ⟨subd0_11_0, List.forall_mem_nil _⟩
theorem ld_okd0_12 : ldCheck G d0_12.U d0_12.ms ldd0_12 = true := by decide +kernel
theorem pre_okd0_12 : subPre G cell0 d0_12 = true := by decide +kernel
theorem subd0_12_0 : subd0_12 [] = true := by decide +kernel
theorem sbd0_12_0 : ∀ q ∈ blkd0_12_0, subd0_12 q = true := by
  unfold blkd0_12_0
  exact List.forall_mem_cons.2 ⟨subd0_12_0, List.forall_mem_nil _⟩
theorem ld_okd0_13 : ldCheck G d0_13.U d0_13.ms ldd0_13 = true := by decide +kernel
theorem pre_okd0_13 : subPre G cell0 d0_13 = true := by decide +kernel
theorem subd0_13_0 : subd0_13 [] = true := by decide +kernel
theorem sbd0_13_0 : ∀ q ∈ blkd0_13_0, subd0_13 q = true := by
  unfold blkd0_13_0
  exact List.forall_mem_cons.2 ⟨subd0_13_0, List.forall_mem_nil _⟩
theorem ld_okd0_14 : ldCheck G d0_14.U d0_14.ms ldd0_14 = true := by decide +kernel
theorem pre_okd0_14 : subPre G cell0 d0_14 = true := by decide +kernel
theorem subd0_14_0 : subd0_14 [] = true := by decide +kernel
theorem sbd0_14_0 : ∀ q ∈ blkd0_14_0, subd0_14 q = true := by
  unfold blkd0_14_0
  exact List.forall_mem_cons.2 ⟨subd0_14_0, List.forall_mem_nil _⟩
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

end ReflectZphi.Data.Cert5.C065
