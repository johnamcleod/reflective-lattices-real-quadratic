import ReflectZphi.Data.Cert5.C113.Base

namespace ReflectZphi.Data.Cert5.C113

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd1_6 : ldCheck G d1_6.U d1_6.ms ldd1_6 = true := by decide +kernel
theorem pre_okd1_6 : subPre G cell1 d1_6 = true := by decide +kernel
theorem subd1_6_0 : subd1_6 [-1] = true := by decide +kernel
theorem subd1_6_1 : subd1_6 [0, -2] = true := by decide +kernel
theorem subd1_6_2 : subd1_6 [0, -1] = true := by decide +kernel
theorem subd1_6_3 : subd1_6 [0, 0] = true := by decide +kernel
theorem subd1_6_4 : subd1_6 [0, 1] = true := by decide +kernel
theorem subd1_6_5 : subd1_6 [1] = true := by decide +kernel
theorem sbd1_6_0 : ∀ q ∈ blkd1_6_0, subd1_6 q = true := by
  unfold blkd1_6_0
  exact List.forall_mem_cons.2 ⟨subd1_6_0, List.forall_mem_cons.2 ⟨subd1_6_1, List.forall_mem_cons.2 ⟨subd1_6_2, List.forall_mem_cons.2 ⟨subd1_6_3, List.forall_mem_cons.2 ⟨subd1_6_4, List.forall_mem_cons.2 ⟨subd1_6_5, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem ld_okd1_7 : ldCheck G d1_7.U d1_7.ms ldd1_7 = true := by decide +kernel
theorem pre_okd1_7 : subPre G cell1 d1_7 = true := by decide +kernel
theorem subd1_7_0 : subd1_7 [-2] = true := by decide +kernel
theorem subd1_7_1 : subd1_7 [-1] = true := by decide +kernel
theorem subd1_7_2 : subd1_7 [0] = true := by decide +kernel
theorem subd1_7_3 : subd1_7 [1] = true := by decide +kernel
theorem subd1_7_4 : subd1_7 [2] = true := by decide +kernel
theorem sbd1_7_0 : ∀ q ∈ blkd1_7_0, subd1_7 q = true := by
  unfold blkd1_7_0
  exact List.forall_mem_cons.2 ⟨subd1_7_0, List.forall_mem_cons.2 ⟨subd1_7_1, List.forall_mem_cons.2 ⟨subd1_7_2, List.forall_mem_cons.2 ⟨subd1_7_3, List.forall_mem_cons.2 ⟨subd1_7_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd1_8 : ldCheck G d1_8.U d1_8.ms ldd1_8 = true := by decide +kernel
theorem pre_okd1_8 : subPre G cell1 d1_8 = true := by decide +kernel
theorem subd1_8_0 : subd1_8 [-2] = true := by decide +kernel
theorem subd1_8_1 : subd1_8 [-1] = true := by decide +kernel
theorem subd1_8_2 : subd1_8 [0] = true := by decide +kernel
theorem subd1_8_3 : subd1_8 [1] = true := by decide +kernel
theorem subd1_8_4 : subd1_8 [2] = true := by decide +kernel
theorem sbd1_8_0 : ∀ q ∈ blkd1_8_0, subd1_8 q = true := by
  unfold blkd1_8_0
  exact List.forall_mem_cons.2 ⟨subd1_8_0, List.forall_mem_cons.2 ⟨subd1_8_1, List.forall_mem_cons.2 ⟨subd1_8_2, List.forall_mem_cons.2 ⟨subd1_8_3, List.forall_mem_cons.2 ⟨subd1_8_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd1_9 : ldCheck G d1_9.U d1_9.ms ldd1_9 = true := by decide +kernel
theorem pre_okd1_9 : subPre G cell1 d1_9 = true := by decide +kernel
theorem subd1_9_0 : subd1_9 [] = true := by decide +kernel
theorem sbd1_9_0 : ∀ q ∈ blkd1_9_0, subd1_9 q = true := by
  unfold blkd1_9_0
  exact List.forall_mem_cons.2 ⟨subd1_9_0, List.forall_mem_nil _⟩
theorem ld_okd2_0 : ldCheck G d2_0.U d2_0.ms ldd2_0 = true := by decide +kernel
theorem pre_okd2_0 : subPre G cell2 d2_0 = true := by decide +kernel
theorem subd2_0_0 : subd2_0 [] = true := by decide +kernel
theorem sbd2_0_0 : ∀ q ∈ blkd2_0_0, subd2_0 q = true := by
  unfold blkd2_0_0
  exact List.forall_mem_cons.2 ⟨subd2_0_0, List.forall_mem_nil _⟩
theorem ld_okd2_1 : ldCheck G d2_1.U d2_1.ms ldd2_1 = true := by decide +kernel
theorem pre_okd2_1 : subPre G cell2 d2_1 = true := by decide +kernel
theorem subd2_1_0 : subd2_1 [] = true := by decide +kernel
theorem sbd2_1_0 : ∀ q ∈ blkd2_1_0, subd2_1 q = true := by
  unfold blkd2_1_0
  exact List.forall_mem_cons.2 ⟨subd2_1_0, List.forall_mem_nil _⟩
theorem ld_okd2_2 : ldCheck G d2_2.U d2_2.ms ldd2_2 = true := by decide +kernel
theorem pre_okd2_2 : subPre G cell2 d2_2 = true := by decide +kernel
theorem subd2_2_0 : subd2_2 [] = true := by decide +kernel
theorem sbd2_2_0 : ∀ q ∈ blkd2_2_0, subd2_2 q = true := by
  unfold blkd2_2_0
  exact List.forall_mem_cons.2 ⟨subd2_2_0, List.forall_mem_nil _⟩
theorem ld_okd2_3 : ldCheck G d2_3.U d2_3.ms ldd2_3 = true := by decide +kernel
theorem pre_okd2_3 : subPre G cell2 d2_3 = true := by decide +kernel
theorem subd2_3_0 : subd2_3 [] = true := by decide +kernel
theorem sbd2_3_0 : ∀ q ∈ blkd2_3_0, subd2_3 q = true := by
  unfold blkd2_3_0
  exact List.forall_mem_cons.2 ⟨subd2_3_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C113
