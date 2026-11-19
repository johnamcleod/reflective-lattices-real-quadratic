import ReflectZphi.Data.Cert5.C123.Base

namespace ReflectZphi.Data.Cert5.C123

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd12_3 : ldCheck G d12_3.U d12_3.ms ldd12_3 = true := by decide +kernel
theorem pre_okd12_3 : subPre G cell12 d12_3 = true := by decide +kernel
theorem subd12_3_0 : subd12_3 [] = true := by decide +kernel
theorem sbd12_3_0 : ∀ q ∈ blkd12_3_0, subd12_3 q = true := by
  unfold blkd12_3_0
  exact List.forall_mem_cons.2 ⟨subd12_3_0, List.forall_mem_nil _⟩
theorem ld_okd12_4 : ldCheck G d12_4.U d12_4.ms ldd12_4 = true := by decide +kernel
theorem pre_okd12_4 : subPre G cell12 d12_4 = true := by decide +kernel
theorem subd12_4_0 : subd12_4 [-2] = true := by decide +kernel
theorem subd12_4_1 : subd12_4 [-1] = true := by decide +kernel
theorem subd12_4_2 : subd12_4 [0, -4] = true := by decide +kernel
theorem subd12_4_3 : subd12_4 [0, -3] = true := by decide +kernel
theorem subd12_4_4 : subd12_4 [0, -2] = true := by decide +kernel
theorem subd12_4_5 : subd12_4 [0, -1] = true := by decide +kernel
theorem subd12_4_6 : subd12_4 [0, 0] = true := by decide +kernel
theorem subd12_4_7 : subd12_4 [0, 1] = true := by decide +kernel
theorem subd12_4_8 : subd12_4 [0, 2] = true := by decide +kernel
theorem subd12_4_9 : subd12_4 [0, 3] = true := by decide +kernel
theorem subd12_4_10 : subd12_4 [1] = true := by decide +kernel
theorem subd12_4_11 : subd12_4 [2] = true := by decide +kernel
theorem sbd12_4_0 : ∀ q ∈ blkd12_4_0, subd12_4 q = true := by
  unfold blkd12_4_0
  exact List.forall_mem_cons.2 ⟨subd12_4_0, List.forall_mem_cons.2 ⟨subd12_4_1, List.forall_mem_cons.2 ⟨subd12_4_2, List.forall_mem_cons.2 ⟨subd12_4_3, List.forall_mem_cons.2 ⟨subd12_4_4, List.forall_mem_cons.2 ⟨subd12_4_5, List.forall_mem_cons.2 ⟨subd12_4_6, List.forall_mem_cons.2 ⟨subd12_4_7, List.forall_mem_cons.2 ⟨subd12_4_8, List.forall_mem_cons.2 ⟨subd12_4_9, List.forall_mem_cons.2 ⟨subd12_4_10, List.forall_mem_cons.2 ⟨subd12_4_11, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd12_5 : ldCheck G d12_5.U d12_5.ms ldd12_5 = true := by decide +kernel
theorem pre_okd12_5 : subPre G cell12 d12_5 = true := by decide +kernel
theorem subd12_5_0 : subd12_5 [-1] = true := by decide +kernel
theorem subd12_5_1 : subd12_5 [0] = true := by decide +kernel
theorem subd12_5_2 : subd12_5 [1] = true := by decide +kernel
theorem sbd12_5_0 : ∀ q ∈ blkd12_5_0, subd12_5 q = true := by
  unfold blkd12_5_0
  exact List.forall_mem_cons.2 ⟨subd12_5_0, List.forall_mem_cons.2 ⟨subd12_5_1, List.forall_mem_cons.2 ⟨subd12_5_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd12_6 : ldCheck G d12_6.U d12_6.ms ldd12_6 = true := by decide +kernel
theorem pre_okd12_6 : subPre G cell12 d12_6 = true := by decide +kernel
theorem subd12_6_0 : subd12_6 [-2] = true := by decide +kernel
theorem subd12_6_1 : subd12_6 [-1, -4] = true := by decide +kernel
theorem subd12_6_2 : subd12_6 [-1, -3] = true := by decide +kernel
theorem subd12_6_3 : subd12_6 [-1, -2] = true := by decide +kernel
theorem subd12_6_4 : subd12_6 [-1, -1] = true := by decide +kernel
theorem subd12_6_5 : subd12_6 [-1, 0] = true := by decide +kernel
theorem subd12_6_6 : subd12_6 [-1, 1] = true := by decide +kernel
theorem subd12_6_7 : subd12_6 [-1, 2] = true := by decide +kernel
theorem subd12_6_8 : subd12_6 [0, -4] = true := by decide +kernel
theorem subd12_6_9 : subd12_6 [0, -3] = true := by decide +kernel
theorem subd12_6_10 : subd12_6 [0, -2] = true := by decide +kernel
theorem subd12_6_11 : subd12_6 [0, -1] = true := by decide +kernel
theorem subd12_6_12 : subd12_6 [0, 0] = true := by decide +kernel
theorem subd12_6_13 : subd12_6 [0, 1] = true := by decide +kernel
theorem subd12_6_14 : subd12_6 [0, 2] = true := by decide +kernel
theorem subd12_6_15 : subd12_6 [0, 3] = true := by decide +kernel
theorem subd12_6_16 : subd12_6 [1, -3] = true := by decide +kernel
theorem subd12_6_17 : subd12_6 [1, -2] = true := by decide +kernel
theorem subd12_6_18 : subd12_6 [1, -1] = true := by decide +kernel
theorem subd12_6_19 : subd12_6 [1, 0] = true := by decide +kernel
theorem subd12_6_20 : subd12_6 [1, 1] = true := by decide +kernel
theorem subd12_6_21 : subd12_6 [1, 2] = true := by decide +kernel
theorem subd12_6_22 : subd12_6 [1, 3] = true := by decide +kernel
theorem subd12_6_23 : subd12_6 [2] = true := by decide +kernel
theorem sbd12_6_0 : ∀ q ∈ blkd12_6_0, subd12_6 q = true := by
  unfold blkd12_6_0
  exact List.forall_mem_cons.2 ⟨subd12_6_0, List.forall_mem_cons.2 ⟨subd12_6_1, List.forall_mem_cons.2 ⟨subd12_6_2, List.forall_mem_cons.2 ⟨subd12_6_3, List.forall_mem_cons.2 ⟨subd12_6_4, List.forall_mem_cons.2 ⟨subd12_6_5, List.forall_mem_cons.2 ⟨subd12_6_6, List.forall_mem_cons.2 ⟨subd12_6_7, List.forall_mem_cons.2 ⟨subd12_6_8, List.forall_mem_cons.2 ⟨subd12_6_9, List.forall_mem_cons.2 ⟨subd12_6_10, List.forall_mem_cons.2 ⟨subd12_6_11, List.forall_mem_cons.2 ⟨subd12_6_12, List.forall_mem_cons.2 ⟨subd12_6_13, List.forall_mem_cons.2 ⟨subd12_6_14, List.forall_mem_cons.2 ⟨subd12_6_15, List.forall_mem_cons.2 ⟨subd12_6_16, List.forall_mem_cons.2 ⟨subd12_6_17, List.forall_mem_cons.2 ⟨subd12_6_18, List.forall_mem_cons.2 ⟨subd12_6_19, List.forall_mem_cons.2 ⟨subd12_6_20, List.forall_mem_cons.2 ⟨subd12_6_21, List.forall_mem_cons.2 ⟨subd12_6_22, List.forall_mem_cons.2 ⟨subd12_6_23, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
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

end ReflectZphi.Data.Cert5.C123
