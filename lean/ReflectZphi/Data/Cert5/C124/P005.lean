import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd2_9_0 : subd2_9 [-2] = true := by decide +kernel
theorem subd2_9_1 : subd2_9 [-1] = true := by decide +kernel
theorem subd2_9_2 : subd2_9 [0, -3] = true := by decide +kernel
theorem subd2_9_3 : subd2_9 [0, -2] = true := by decide +kernel
theorem subd2_9_4 : subd2_9 [0, -1] = true := by decide +kernel
theorem subd2_9_5 : subd2_9 [0, 0] = true := by decide +kernel
theorem subd2_9_6 : subd2_9 [0, 1] = true := by decide +kernel
theorem subd2_9_7 : subd2_9 [0, 2] = true := by decide +kernel
theorem subd2_9_8 : subd2_9 [1] = true := by decide +kernel
theorem subd2_9_9 : subd2_9 [2] = true := by decide +kernel
theorem sbd2_9_0 : ∀ q ∈ blkd2_9_0, subd2_9 q = true := by
  unfold blkd2_9_0
  exact List.forall_mem_cons.2 ⟨subd2_9_0, List.forall_mem_cons.2 ⟨subd2_9_1, List.forall_mem_cons.2 ⟨subd2_9_2, List.forall_mem_cons.2 ⟨subd2_9_3, List.forall_mem_cons.2 ⟨subd2_9_4, List.forall_mem_cons.2 ⟨subd2_9_5, List.forall_mem_cons.2 ⟨subd2_9_6, List.forall_mem_cons.2 ⟨subd2_9_7, List.forall_mem_cons.2 ⟨subd2_9_8, List.forall_mem_cons.2 ⟨subd2_9_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd2_10 : ldCheck G d2_10.U d2_10.ms ldd2_10 = true := by decide +kernel
theorem pre_okd2_10 : subPre G cell2 d2_10 = true := by decide +kernel
theorem subd2_10_0 : subd2_10 [-2] = true := by decide +kernel
theorem subd2_10_1 : subd2_10 [-1] = true := by decide +kernel
theorem subd2_10_2 : subd2_10 [0] = true := by decide +kernel
theorem subd2_10_3 : subd2_10 [1] = true := by decide +kernel
theorem subd2_10_4 : subd2_10 [2] = true := by decide +kernel
theorem sbd2_10_0 : ∀ q ∈ blkd2_10_0, subd2_10 q = true := by
  unfold blkd2_10_0
  exact List.forall_mem_cons.2 ⟨subd2_10_0, List.forall_mem_cons.2 ⟨subd2_10_1, List.forall_mem_cons.2 ⟨subd2_10_2, List.forall_mem_cons.2 ⟨subd2_10_3, List.forall_mem_cons.2 ⟨subd2_10_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd2_11 : ldCheck G d2_11.U d2_11.ms ldd2_11 = true := by decide +kernel
theorem pre_okd2_11 : subPre G cell2 d2_11 = true := by decide +kernel
theorem subd2_11_0 : subd2_11 [-1] = true := by decide +kernel
theorem subd2_11_1 : subd2_11 [0] = true := by decide +kernel
theorem subd2_11_2 : subd2_11 [1] = true := by decide +kernel
theorem sbd2_11_0 : ∀ q ∈ blkd2_11_0, subd2_11 q = true := by
  unfold blkd2_11_0
  exact List.forall_mem_cons.2 ⟨subd2_11_0, List.forall_mem_cons.2 ⟨subd2_11_1, List.forall_mem_cons.2 ⟨subd2_11_2, List.forall_mem_nil _⟩⟩⟩
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
theorem ld_okd2_14 : ldCheck G d2_14.U d2_14.ms ldd2_14 = true := by decide +kernel
theorem pre_okd2_14 : subPre G cell2 d2_14 = true := by decide +kernel
theorem subd2_14_0 : subd2_14 [-1] = true := by decide +kernel
theorem subd2_14_1 : subd2_14 [0, -2] = true := by decide +kernel
theorem subd2_14_2 : subd2_14 [0, -1] = true := by decide +kernel
theorem subd2_14_3 : subd2_14 [0, 0] = true := by decide +kernel
theorem subd2_14_4 : subd2_14 [0, 1] = true := by decide +kernel
theorem subd2_14_5 : subd2_14 [1] = true := by decide +kernel
theorem sbd2_14_0 : ∀ q ∈ blkd2_14_0, subd2_14 q = true := by
  unfold blkd2_14_0
  exact List.forall_mem_cons.2 ⟨subd2_14_0, List.forall_mem_cons.2 ⟨subd2_14_1, List.forall_mem_cons.2 ⟨subd2_14_2, List.forall_mem_cons.2 ⟨subd2_14_3, List.forall_mem_cons.2 ⟨subd2_14_4, List.forall_mem_cons.2 ⟨subd2_14_5, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
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

end ReflectZphi.Data.Cert5.C124
