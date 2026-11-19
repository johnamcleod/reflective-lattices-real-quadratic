import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd1_9 : ldCheck G d1_9.U d1_9.ms ldd1_9 = true := by decide +kernel
theorem pre_okd1_9 : subPre G cell1 d1_9 = true := by decide +kernel
theorem subd1_9_0 : subd1_9 [-2] = true := by decide +kernel
theorem subd1_9_1 : subd1_9 [-1] = true := by decide +kernel
theorem subd1_9_2 : subd1_9 [0] = true := by decide +kernel
theorem subd1_9_3 : subd1_9 [1] = true := by decide +kernel
theorem subd1_9_4 : subd1_9 [2] = true := by decide +kernel
theorem sbd1_9_0 : ∀ q ∈ blkd1_9_0, subd1_9 q = true := by
  unfold blkd1_9_0
  exact List.forall_mem_cons.2 ⟨subd1_9_0, List.forall_mem_cons.2 ⟨subd1_9_1, List.forall_mem_cons.2 ⟨subd1_9_2, List.forall_mem_cons.2 ⟨subd1_9_3, List.forall_mem_cons.2 ⟨subd1_9_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd1_10 : ldCheck G d1_10.U d1_10.ms ldd1_10 = true := by decide +kernel
theorem pre_okd1_10 : subPre G cell1 d1_10 = true := by decide +kernel
theorem subd1_10_0 : subd1_10 [-1] = true := by decide +kernel
theorem subd1_10_1 : subd1_10 [0] = true := by decide +kernel
theorem subd1_10_2 : subd1_10 [1] = true := by decide +kernel
theorem sbd1_10_0 : ∀ q ∈ blkd1_10_0, subd1_10 q = true := by
  unfold blkd1_10_0
  exact List.forall_mem_cons.2 ⟨subd1_10_0, List.forall_mem_cons.2 ⟨subd1_10_1, List.forall_mem_cons.2 ⟨subd1_10_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd1_11 : ldCheck G d1_11.U d1_11.ms ldd1_11 = true := by decide +kernel
theorem pre_okd1_11 : subPre G cell1 d1_11 = true := by decide +kernel
theorem subd1_11_0 : subd1_11 [-1] = true := by decide +kernel
theorem subd1_11_1 : subd1_11 [0] = true := by decide +kernel
theorem subd1_11_2 : subd1_11 [1] = true := by decide +kernel
theorem sbd1_11_0 : ∀ q ∈ blkd1_11_0, subd1_11 q = true := by
  unfold blkd1_11_0
  exact List.forall_mem_cons.2 ⟨subd1_11_0, List.forall_mem_cons.2 ⟨subd1_11_1, List.forall_mem_cons.2 ⟨subd1_11_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd1_12 : ldCheck G d1_12.U d1_12.ms ldd1_12 = true := by decide +kernel
theorem pre_okd1_12 : subPre G cell1 d1_12 = true := by decide +kernel
theorem subd1_12_0 : subd1_12 [] = true := by decide +kernel
theorem sbd1_12_0 : ∀ q ∈ blkd1_12_0, subd1_12 q = true := by
  unfold blkd1_12_0
  exact List.forall_mem_cons.2 ⟨subd1_12_0, List.forall_mem_nil _⟩
theorem ld_okd1_13 : ldCheck G d1_13.U d1_13.ms ldd1_13 = true := by decide +kernel
theorem pre_okd1_13 : subPre G cell1 d1_13 = true := by decide +kernel
theorem subd1_13_0 : subd1_13 [] = true := by decide +kernel
theorem sbd1_13_0 : ∀ q ∈ blkd1_13_0, subd1_13 q = true := by
  unfold blkd1_13_0
  exact List.forall_mem_cons.2 ⟨subd1_13_0, List.forall_mem_nil _⟩
theorem ld_okd1_14 : ldCheck G d1_14.U d1_14.ms ldd1_14 = true := by decide +kernel
theorem pre_okd1_14 : subPre G cell1 d1_14 = true := by decide +kernel
theorem subd1_14_0 : subd1_14 [-2] = true := by decide +kernel
theorem subd1_14_1 : subd1_14 [-1] = true := by decide +kernel
theorem subd1_14_2 : subd1_14 [0] = true := by decide +kernel
theorem subd1_14_3 : subd1_14 [1] = true := by decide +kernel
theorem subd1_14_4 : subd1_14 [2] = true := by decide +kernel
theorem sbd1_14_0 : ∀ q ∈ blkd1_14_0, subd1_14 q = true := by
  unfold blkd1_14_0
  exact List.forall_mem_cons.2 ⟨subd1_14_0, List.forall_mem_cons.2 ⟨subd1_14_1, List.forall_mem_cons.2 ⟨subd1_14_2, List.forall_mem_cons.2 ⟨subd1_14_3, List.forall_mem_cons.2 ⟨subd1_14_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
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

end ReflectZphi.Data.Cert5.C124
