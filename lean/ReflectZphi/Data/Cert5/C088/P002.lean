import ReflectZphi.Data.Cert5.C088.Base

namespace ReflectZphi.Data.Cert5.C088

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

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
theorem ld_okd1_6 : ldCheck G d1_6.U d1_6.ms ldd1_6 = true := by decide +kernel
theorem pre_okd1_6 : subPre G cell1 d1_6 = true := by decide +kernel
theorem subd1_6_0 : subd1_6 [] = true := by decide +kernel
theorem sbd1_6_0 : ∀ q ∈ blkd1_6_0, subd1_6 q = true := by
  unfold blkd1_6_0
  exact List.forall_mem_cons.2 ⟨subd1_6_0, List.forall_mem_nil _⟩
theorem ld_okd1_7 : ldCheck G d1_7.U d1_7.ms ldd1_7 = true := by decide +kernel
theorem pre_okd1_7 : subPre G cell1 d1_7 = true := by decide +kernel
theorem subd1_7_0 : subd1_7 [] = true := by decide +kernel
theorem sbd1_7_0 : ∀ q ∈ blkd1_7_0, subd1_7 q = true := by
  unfold blkd1_7_0
  exact List.forall_mem_cons.2 ⟨subd1_7_0, List.forall_mem_nil _⟩
theorem ld_okd1_8 : ldCheck G d1_8.U d1_8.ms ldd1_8 = true := by decide +kernel
theorem pre_okd1_8 : subPre G cell1 d1_8 = true := by decide +kernel
theorem subd1_8_0 : subd1_8 [] = true := by decide +kernel
theorem sbd1_8_0 : ∀ q ∈ blkd1_8_0, subd1_8 q = true := by
  unfold blkd1_8_0
  exact List.forall_mem_cons.2 ⟨subd1_8_0, List.forall_mem_nil _⟩
theorem ld_okd1_9 : ldCheck G d1_9.U d1_9.ms ldd1_9 = true := by decide +kernel
theorem pre_okd1_9 : subPre G cell1 d1_9 = true := by decide +kernel
theorem subd1_9_0 : subd1_9 [] = true := by decide +kernel
theorem sbd1_9_0 : ∀ q ∈ blkd1_9_0, subd1_9 q = true := by
  unfold blkd1_9_0
  exact List.forall_mem_cons.2 ⟨subd1_9_0, List.forall_mem_nil _⟩
theorem ld_okd1_10 : ldCheck G d1_10.U d1_10.ms ldd1_10 = true := by decide +kernel
theorem pre_okd1_10 : subPre G cell1 d1_10 = true := by decide +kernel
theorem subd1_10_0 : subd1_10 [] = true := by decide +kernel
theorem sbd1_10_0 : ∀ q ∈ blkd1_10_0, subd1_10 q = true := by
  unfold blkd1_10_0
  exact List.forall_mem_cons.2 ⟨subd1_10_0, List.forall_mem_nil _⟩
theorem ld_okd1_11 : ldCheck G d1_11.U d1_11.ms ldd1_11 = true := by decide +kernel
theorem pre_okd1_11 : subPre G cell1 d1_11 = true := by decide +kernel
theorem subd1_11_0 : subd1_11 [] = true := by decide +kernel
theorem sbd1_11_0 : ∀ q ∈ blkd1_11_0, subd1_11 q = true := by
  unfold blkd1_11_0
  exact List.forall_mem_cons.2 ⟨subd1_11_0, List.forall_mem_nil _⟩
theorem ld_okd1_12 : ldCheck G d1_12.U d1_12.ms ldd1_12 = true := by decide +kernel
theorem pre_okd1_12 : subPre G cell1 d1_12 = true := by decide +kernel
theorem subd1_12_0 : subd1_12 [] = true := by decide +kernel
theorem sbd1_12_0 : ∀ q ∈ blkd1_12_0, subd1_12 q = true := by
  unfold blkd1_12_0
  exact List.forall_mem_cons.2 ⟨subd1_12_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C088
