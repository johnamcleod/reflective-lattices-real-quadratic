import ReflectZphi.Data.Cert5.C108.Base

namespace ReflectZphi.Data.Cert5.C108

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd0_0 : ldCheck G d0_0.U d0_0.ms ldd0_0 = true := by decide +kernel
theorem pre_okd0_0 : subPre G cell0 d0_0 = true := by decide +kernel
theorem subd0_0_0 : subd0_0 [] = true := by decide +kernel
theorem sbd0_0_0 : ∀ q ∈ blkd0_0_0, subd0_0 q = true := by
  unfold blkd0_0_0
  exact List.forall_mem_cons.2 ⟨subd0_0_0, List.forall_mem_nil _⟩
theorem ld_okd0_1 : ldCheck G d0_1.U d0_1.ms ldd0_1 = true := by decide +kernel
theorem pre_okd0_1 : subPre G cell0 d0_1 = true := by decide +kernel
theorem subd0_1_0 : subd0_1 [] = true := by decide +kernel
theorem sbd0_1_0 : ∀ q ∈ blkd0_1_0, subd0_1 q = true := by
  unfold blkd0_1_0
  exact List.forall_mem_cons.2 ⟨subd0_1_0, List.forall_mem_nil _⟩
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
theorem ld_okd0_4 : ldCheck G d0_4.U d0_4.ms ldd0_4 = true := by decide +kernel
theorem pre_okd0_4 : subPre G cell0 d0_4 = true := by decide +kernel
theorem subd0_4_0 : subd0_4 [] = true := by decide +kernel
theorem sbd0_4_0 : ∀ q ∈ blkd0_4_0, subd0_4 q = true := by
  unfold blkd0_4_0
  exact List.forall_mem_cons.2 ⟨subd0_4_0, List.forall_mem_nil _⟩
theorem ld_okd0_5 : ldCheck G d0_5.U d0_5.ms ldd0_5 = true := by decide +kernel
theorem pre_okd0_5 : subPre G cell0 d0_5 = true := by decide +kernel
theorem subd0_5_0 : subd0_5 [] = true := by decide +kernel
theorem sbd0_5_0 : ∀ q ∈ blkd0_5_0, subd0_5 q = true := by
  unfold blkd0_5_0
  exact List.forall_mem_cons.2 ⟨subd0_5_0, List.forall_mem_nil _⟩
theorem ld_okd0_6 : ldCheck G d0_6.U d0_6.ms ldd0_6 = true := by decide +kernel
theorem pre_okd0_6 : subPre G cell0 d0_6 = true := by decide +kernel
theorem subd0_6_0 : subd0_6 [] = true := by decide +kernel
theorem sbd0_6_0 : ∀ q ∈ blkd0_6_0, subd0_6 q = true := by
  unfold blkd0_6_0
  exact List.forall_mem_cons.2 ⟨subd0_6_0, List.forall_mem_nil _⟩
theorem ld_okd0_7 : ldCheck G d0_7.U d0_7.ms ldd0_7 = true := by decide +kernel
theorem pre_okd0_7 : subPre G cell0 d0_7 = true := by decide +kernel
theorem subd0_7_0 : subd0_7 [] = true := by decide +kernel
theorem sbd0_7_0 : ∀ q ∈ blkd0_7_0, subd0_7 q = true := by
  unfold blkd0_7_0
  exact List.forall_mem_cons.2 ⟨subd0_7_0, List.forall_mem_nil _⟩
theorem ld_okd1_0 : ldCheck G d1_0.U d1_0.ms ldd1_0 = true := by decide +kernel
theorem pre_okd1_0 : subPre G cell1 d1_0 = true := by decide +kernel
theorem subd1_0_0 : subd1_0 [] = true := by decide +kernel
theorem sbd1_0_0 : ∀ q ∈ blkd1_0_0, subd1_0 q = true := by
  unfold blkd1_0_0
  exact List.forall_mem_cons.2 ⟨subd1_0_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C108
