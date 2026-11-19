import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd12_14_0 : subd12_14 [-3] = true := by decide +kernel
theorem subd12_14_1 : subd12_14 [-2] = true := by decide +kernel
theorem subd12_14_2 : subd12_14 [-1] = true := by decide +kernel
theorem subd12_14_3 : subd12_14 [0, -4] = true := by decide +kernel
theorem subd12_14_4 : subd12_14 [0, -3] = true := by decide +kernel
theorem subd12_14_5 : subd12_14 [0, -2] = true := by decide +kernel
theorem subd12_14_6 : subd12_14 [0, -1] = true := by decide +kernel
theorem subd12_14_7 : subd12_14 [0, 0] = true := by decide +kernel
theorem subd12_14_8 : subd12_14 [0, 1] = true := by decide +kernel
theorem subd12_14_9 : subd12_14 [0, 2] = true := by decide +kernel
theorem subd12_14_10 : subd12_14 [0, 3] = true := by decide +kernel
theorem subd12_14_11 : subd12_14 [1] = true := by decide +kernel
theorem subd12_14_12 : subd12_14 [2] = true := by decide +kernel
theorem subd12_14_13 : subd12_14 [3] = true := by decide +kernel
theorem sbd12_14_0 : ∀ q ∈ blkd12_14_0, subd12_14 q = true := by
  unfold blkd12_14_0
  exact List.forall_mem_cons.2 ⟨subd12_14_0, List.forall_mem_cons.2 ⟨subd12_14_1, List.forall_mem_cons.2 ⟨subd12_14_2, List.forall_mem_cons.2 ⟨subd12_14_3, List.forall_mem_cons.2 ⟨subd12_14_4, List.forall_mem_cons.2 ⟨subd12_14_5, List.forall_mem_cons.2 ⟨subd12_14_6, List.forall_mem_cons.2 ⟨subd12_14_7, List.forall_mem_cons.2 ⟨subd12_14_8, List.forall_mem_cons.2 ⟨subd12_14_9, List.forall_mem_cons.2 ⟨subd12_14_10, List.forall_mem_cons.2 ⟨subd12_14_11, List.forall_mem_cons.2 ⟨subd12_14_12, List.forall_mem_cons.2 ⟨subd12_14_13, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd13_0 : ldCheck G d13_0.U d13_0.ms ldd13_0 = true := by decide +kernel
theorem pre_okd13_0 : subPre G cell13 d13_0 = true := by decide +kernel
theorem subd13_0_0 : subd13_0 [] = true := by decide +kernel
theorem sbd13_0_0 : ∀ q ∈ blkd13_0_0, subd13_0 q = true := by
  unfold blkd13_0_0
  exact List.forall_mem_cons.2 ⟨subd13_0_0, List.forall_mem_nil _⟩
theorem ld_okd13_1 : ldCheck G d13_1.U d13_1.ms ldd13_1 = true := by decide +kernel
theorem pre_okd13_1 : subPre G cell13 d13_1 = true := by decide +kernel
theorem subd13_1_0 : subd13_1 [] = true := by decide +kernel
theorem sbd13_1_0 : ∀ q ∈ blkd13_1_0, subd13_1 q = true := by
  unfold blkd13_1_0
  exact List.forall_mem_cons.2 ⟨subd13_1_0, List.forall_mem_nil _⟩
theorem ld_okd13_2 : ldCheck G d13_2.U d13_2.ms ldd13_2 = true := by decide +kernel
theorem pre_okd13_2 : subPre G cell13 d13_2 = true := by decide +kernel
theorem subd13_2_0 : subd13_2 [] = true := by decide +kernel
theorem sbd13_2_0 : ∀ q ∈ blkd13_2_0, subd13_2 q = true := by
  unfold blkd13_2_0
  exact List.forall_mem_cons.2 ⟨subd13_2_0, List.forall_mem_nil _⟩
theorem ld_okd13_3 : ldCheck G d13_3.U d13_3.ms ldd13_3 = true := by decide +kernel
theorem pre_okd13_3 : subPre G cell13 d13_3 = true := by decide +kernel
theorem subd13_3_0 : subd13_3 [] = true := by decide +kernel
theorem sbd13_3_0 : ∀ q ∈ blkd13_3_0, subd13_3 q = true := by
  unfold blkd13_3_0
  exact List.forall_mem_cons.2 ⟨subd13_3_0, List.forall_mem_nil _⟩
theorem ld_okd13_4 : ldCheck G d13_4.U d13_4.ms ldd13_4 = true := by decide +kernel
theorem pre_okd13_4 : subPre G cell13 d13_4 = true := by decide +kernel
theorem subd13_4_0 : subd13_4 [] = true := by decide +kernel
theorem sbd13_4_0 : ∀ q ∈ blkd13_4_0, subd13_4 q = true := by
  unfold blkd13_4_0
  exact List.forall_mem_cons.2 ⟨subd13_4_0, List.forall_mem_nil _⟩
theorem ld_okd13_5 : ldCheck G d13_5.U d13_5.ms ldd13_5 = true := by decide +kernel
theorem pre_okd13_5 : subPre G cell13 d13_5 = true := by decide +kernel
theorem subd13_5_0 : subd13_5 [] = true := by decide +kernel
theorem sbd13_5_0 : ∀ q ∈ blkd13_5_0, subd13_5 q = true := by
  unfold blkd13_5_0
  exact List.forall_mem_cons.2 ⟨subd13_5_0, List.forall_mem_nil _⟩
theorem ld_okd13_6 : ldCheck G d13_6.U d13_6.ms ldd13_6 = true := by decide +kernel
theorem pre_okd13_6 : subPre G cell13 d13_6 = true := by decide +kernel
theorem subd13_6_0 : subd13_6 [-2] = true := by decide +kernel
theorem subd13_6_1 : subd13_6 [-1] = true := by decide +kernel
theorem subd13_6_2 : subd13_6 [0] = true := by decide +kernel
theorem subd13_6_3 : subd13_6 [1] = true := by decide +kernel
theorem subd13_6_4 : subd13_6 [2] = true := by decide +kernel
theorem sbd13_6_0 : ∀ q ∈ blkd13_6_0, subd13_6 q = true := by
  unfold blkd13_6_0
  exact List.forall_mem_cons.2 ⟨subd13_6_0, List.forall_mem_cons.2 ⟨subd13_6_1, List.forall_mem_cons.2 ⟨subd13_6_2, List.forall_mem_cons.2 ⟨subd13_6_3, List.forall_mem_cons.2 ⟨subd13_6_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd13_7 : ldCheck G d13_7.U d13_7.ms ldd13_7 = true := by decide +kernel
theorem pre_okd13_7 : subPre G cell13 d13_7 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C124
