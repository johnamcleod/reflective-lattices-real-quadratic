import ReflectZphi.Data.Cert5.C065.Base

namespace ReflectZphi.Data.Cert5.C065

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

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
theorem ld_okd2_4 : ldCheck G d2_4.U d2_4.ms ldd2_4 = true := by decide +kernel
theorem pre_okd2_4 : subPre G cell2 d2_4 = true := by decide +kernel
theorem subd2_4_0 : subd2_4 [] = true := by decide +kernel
theorem sbd2_4_0 : ∀ q ∈ blkd2_4_0, subd2_4 q = true := by
  unfold blkd2_4_0
  exact List.forall_mem_cons.2 ⟨subd2_4_0, List.forall_mem_nil _⟩
theorem ld_okd2_5 : ldCheck G d2_5.U d2_5.ms ldd2_5 = true := by decide +kernel
theorem pre_okd2_5 : subPre G cell2 d2_5 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C065
