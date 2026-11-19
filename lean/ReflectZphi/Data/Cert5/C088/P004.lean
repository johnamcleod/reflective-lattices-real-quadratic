import ReflectZphi.Data.Cert5.C088.Base

namespace ReflectZphi.Data.Cert5.C088

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd2_8 : ldCheck G d2_8.U d2_8.ms ldd2_8 = true := by decide +kernel
theorem pre_okd2_8 : subPre G cell2 d2_8 = true := by decide +kernel
theorem subd2_8_0 : subd2_8 [] = true := by decide +kernel
theorem sbd2_8_0 : ∀ q ∈ blkd2_8_0, subd2_8 q = true := by
  unfold blkd2_8_0
  exact List.forall_mem_cons.2 ⟨subd2_8_0, List.forall_mem_nil _⟩
theorem ld_okd2_9 : ldCheck G d2_9.U d2_9.ms ldd2_9 = true := by decide +kernel
theorem pre_okd2_9 : subPre G cell2 d2_9 = true := by decide +kernel
theorem subd2_9_0 : subd2_9 [] = true := by decide +kernel
theorem sbd2_9_0 : ∀ q ∈ blkd2_9_0, subd2_9 q = true := by
  unfold blkd2_9_0
  exact List.forall_mem_cons.2 ⟨subd2_9_0, List.forall_mem_nil _⟩
theorem ld_okd2_10 : ldCheck G d2_10.U d2_10.ms ldd2_10 = true := by decide +kernel
theorem pre_okd2_10 : subPre G cell2 d2_10 = true := by decide +kernel
theorem subd2_10_0 : subd2_10 [] = true := by decide +kernel
theorem sbd2_10_0 : ∀ q ∈ blkd2_10_0, subd2_10 q = true := by
  unfold blkd2_10_0
  exact List.forall_mem_cons.2 ⟨subd2_10_0, List.forall_mem_nil _⟩
theorem ld_okd2_11 : ldCheck G d2_11.U d2_11.ms ldd2_11 = true := by decide +kernel
theorem pre_okd2_11 : subPre G cell2 d2_11 = true := by decide +kernel
theorem subd2_11_0 : subd2_11 [] = true := by decide +kernel
theorem sbd2_11_0 : ∀ q ∈ blkd2_11_0, subd2_11 q = true := by
  unfold blkd2_11_0
  exact List.forall_mem_cons.2 ⟨subd2_11_0, List.forall_mem_nil _⟩
theorem ld_okd2_12 : ldCheck G d2_12.U d2_12.ms ldd2_12 = true := by decide +kernel
theorem pre_okd2_12 : subPre G cell2 d2_12 = true := by decide +kernel
theorem subd2_12_0 : subd2_12 [] = true := by decide +kernel
theorem sbd2_12_0 : ∀ q ∈ blkd2_12_0, subd2_12 q = true := by
  unfold blkd2_12_0
  exact List.forall_mem_cons.2 ⟨subd2_12_0, List.forall_mem_nil _⟩
theorem ld_okd2_13 : ldCheck G d2_13.U d2_13.ms ldd2_13 = true := by decide +kernel
theorem pre_okd2_13 : subPre G cell2 d2_13 = true := by decide +kernel
theorem subd2_13_0 : subd2_13 [] = true := by decide +kernel
theorem sbd2_13_0 : ∀ q ∈ blkd2_13_0, subd2_13 q = true := by
  unfold blkd2_13_0
  exact List.forall_mem_cons.2 ⟨subd2_13_0, List.forall_mem_nil _⟩
theorem ld_okd3_0 : ldCheck G d3_0.U d3_0.ms ldd3_0 = true := by decide +kernel
theorem pre_okd3_0 : subPre G cell3 d3_0 = true := by decide +kernel
theorem subd3_0_0 : subd3_0 [] = true := by decide +kernel
theorem sbd3_0_0 : ∀ q ∈ blkd3_0_0, subd3_0 q = true := by
  unfold blkd3_0_0
  exact List.forall_mem_cons.2 ⟨subd3_0_0, List.forall_mem_nil _⟩
theorem ld_okd3_1 : ldCheck G d3_1.U d3_1.ms ldd3_1 = true := by decide +kernel
theorem pre_okd3_1 : subPre G cell3 d3_1 = true := by decide +kernel
theorem subd3_1_0 : subd3_1 [] = true := by decide +kernel
theorem sbd3_1_0 : ∀ q ∈ blkd3_1_0, subd3_1 q = true := by
  unfold blkd3_1_0
  exact List.forall_mem_cons.2 ⟨subd3_1_0, List.forall_mem_nil _⟩
theorem ld_okd3_2 : ldCheck G d3_2.U d3_2.ms ldd3_2 = true := by decide +kernel
theorem pre_okd3_2 : subPre G cell3 d3_2 = true := by decide +kernel
theorem subd3_2_0 : subd3_2 [] = true := by decide +kernel
theorem sbd3_2_0 : ∀ q ∈ blkd3_2_0, subd3_2 q = true := by
  unfold blkd3_2_0
  exact List.forall_mem_cons.2 ⟨subd3_2_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C088
