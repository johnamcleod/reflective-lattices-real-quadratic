import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

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
theorem ld_okd1_6 : ldCheck G d1_6.U d1_6.ms ldd1_6 = true := by decide +kernel
theorem pre_okd1_6 : subPre G cell1 d1_6 = true := by decide +kernel
theorem subd1_6_0 : subd1_6 [-2] = true := by decide +kernel
theorem subd1_6_1 : subd1_6 [-1] = true := by decide +kernel
theorem subd1_6_2 : subd1_6 [0] = true := by decide +kernel
theorem subd1_6_3 : subd1_6 [1] = true := by decide +kernel
theorem subd1_6_4 : subd1_6 [2] = true := by decide +kernel
theorem sbd1_6_0 : ∀ q ∈ blkd1_6_0, subd1_6 q = true := by
  unfold blkd1_6_0
  exact List.forall_mem_cons.2 ⟨subd1_6_0, List.forall_mem_cons.2 ⟨subd1_6_1, List.forall_mem_cons.2 ⟨subd1_6_2, List.forall_mem_cons.2 ⟨subd1_6_3, List.forall_mem_cons.2 ⟨subd1_6_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd1_7 : ldCheck G d1_7.U d1_7.ms ldd1_7 = true := by decide +kernel
theorem pre_okd1_7 : subPre G cell1 d1_7 = true := by decide +kernel
theorem subd1_7_0 : subd1_7 [-1] = true := by decide +kernel
theorem subd1_7_1 : subd1_7 [0] = true := by decide +kernel
theorem subd1_7_2 : subd1_7 [1] = true := by decide +kernel
theorem sbd1_7_0 : ∀ q ∈ blkd1_7_0, subd1_7 q = true := by
  unfold blkd1_7_0
  exact List.forall_mem_cons.2 ⟨subd1_7_0, List.forall_mem_cons.2 ⟨subd1_7_1, List.forall_mem_cons.2 ⟨subd1_7_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd1_8 : ldCheck G d1_8.U d1_8.ms ldd1_8 = true := by decide +kernel
theorem pre_okd1_8 : subPre G cell1 d1_8 = true := by decide +kernel
theorem subd1_8_0 : subd1_8 [-1] = true := by decide +kernel
theorem subd1_8_1 : subd1_8 [0] = true := by decide +kernel
theorem subd1_8_2 : subd1_8 [1] = true := by decide +kernel
theorem sbd1_8_0 : ∀ q ∈ blkd1_8_0, subd1_8 q = true := by
  unfold blkd1_8_0
  exact List.forall_mem_cons.2 ⟨subd1_8_0, List.forall_mem_cons.2 ⟨subd1_8_1, List.forall_mem_cons.2 ⟨subd1_8_2, List.forall_mem_nil _⟩⟩⟩

end ReflectZphi.Data.Cert5.C124
