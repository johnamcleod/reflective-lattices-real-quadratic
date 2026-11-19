import ReflectZphi.Data.Cert5.C110.Base

namespace ReflectZphi.Data.Cert5.C110

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd12_2_0 : subd12_2 [-3] = true := by decide +kernel
theorem subd12_2_1 : subd12_2 [-2] = true := by decide +kernel
theorem subd12_2_2 : subd12_2 [-1, -4] = true := by decide +kernel
theorem subd12_2_3 : subd12_2 [-1, -3] = true := by decide +kernel
theorem subd12_2_4 : subd12_2 [-1, -2] = true := by decide +kernel
theorem subd12_2_5 : subd12_2 [-1, -1] = true := by decide +kernel
theorem subd12_2_6 : subd12_2 [-1, 0] = true := by decide +kernel
theorem subd12_2_7 : subd12_2 [-1, 1] = true := by decide +kernel
theorem subd12_2_8 : subd12_2 [-1, 2] = true := by decide +kernel
theorem subd12_2_9 : subd12_2 [-1, 3] = true := by decide +kernel
theorem subd12_2_10 : subd12_2 [0, -4] = true := by decide +kernel
theorem subd12_2_11 : subd12_2 [0, -3] = true := by decide +kernel
theorem subd12_2_12 : subd12_2 [0, -2] = true := by decide +kernel
theorem subd12_2_13 : subd12_2 [0, -1] = true := by decide +kernel
theorem subd12_2_14 : subd12_2 [0, 0] = true := by decide +kernel
theorem subd12_2_15 : subd12_2 [0, 1] = true := by decide +kernel
theorem subd12_2_16 : subd12_2 [0, 2] = true := by decide +kernel
theorem subd12_2_17 : subd12_2 [0, 3] = true := by decide +kernel
theorem subd12_2_18 : subd12_2 [1, -4] = true := by decide +kernel
theorem subd12_2_19 : subd12_2 [1, -3] = true := by decide +kernel
theorem subd12_2_20 : subd12_2 [1, -2] = true := by decide +kernel
theorem subd12_2_21 : subd12_2 [1, -1] = true := by decide +kernel
theorem subd12_2_22 : subd12_2 [1, 0] = true := by decide +kernel
theorem subd12_2_23 : subd12_2 [1, 1] = true := by decide +kernel
theorem subd12_2_24 : subd12_2 [1, 2] = true := by decide +kernel
theorem subd12_2_25 : subd12_2 [1, 3] = true := by decide +kernel
theorem subd12_2_26 : subd12_2 [2] = true := by decide +kernel
theorem subd12_2_27 : subd12_2 [3] = true := by decide +kernel
theorem sbd12_2_0 : ∀ q ∈ blkd12_2_0, subd12_2 q = true := by
  unfold blkd12_2_0
  exact List.forall_mem_cons.2 ⟨subd12_2_0, List.forall_mem_cons.2 ⟨subd12_2_1, List.forall_mem_cons.2 ⟨subd12_2_2, List.forall_mem_cons.2 ⟨subd12_2_3, List.forall_mem_cons.2 ⟨subd12_2_4, List.forall_mem_cons.2 ⟨subd12_2_5, List.forall_mem_cons.2 ⟨subd12_2_6, List.forall_mem_cons.2 ⟨subd12_2_7, List.forall_mem_cons.2 ⟨subd12_2_8, List.forall_mem_cons.2 ⟨subd12_2_9, List.forall_mem_cons.2 ⟨subd12_2_10, List.forall_mem_cons.2 ⟨subd12_2_11, List.forall_mem_cons.2 ⟨subd12_2_12, List.forall_mem_cons.2 ⟨subd12_2_13, List.forall_mem_cons.2 ⟨subd12_2_14, List.forall_mem_cons.2 ⟨subd12_2_15, List.forall_mem_cons.2 ⟨subd12_2_16, List.forall_mem_cons.2 ⟨subd12_2_17, List.forall_mem_cons.2 ⟨subd12_2_18, List.forall_mem_cons.2 ⟨subd12_2_19, List.forall_mem_cons.2 ⟨subd12_2_20, List.forall_mem_cons.2 ⟨subd12_2_21, List.forall_mem_cons.2 ⟨subd12_2_22, List.forall_mem_cons.2 ⟨subd12_2_23, List.forall_mem_cons.2 ⟨subd12_2_24, List.forall_mem_cons.2 ⟨subd12_2_25, List.forall_mem_cons.2 ⟨subd12_2_26, List.forall_mem_cons.2 ⟨subd12_2_27, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd12_3 : ldCheck G d12_3.U d12_3.ms ldd12_3 = true := by decide +kernel
theorem pre_okd12_3 : subPre G cell12 d12_3 = true := by decide +kernel
theorem subd12_3_0 : subd12_3 [-2] = true := by decide +kernel
theorem subd12_3_1 : subd12_3 [-1] = true := by decide +kernel
theorem subd12_3_2 : subd12_3 [0] = true := by decide +kernel
theorem subd12_3_3 : subd12_3 [1] = true := by decide +kernel
theorem subd12_3_4 : subd12_3 [2] = true := by decide +kernel
theorem sbd12_3_0 : ∀ q ∈ blkd12_3_0, subd12_3 q = true := by
  unfold blkd12_3_0
  exact List.forall_mem_cons.2 ⟨subd12_3_0, List.forall_mem_cons.2 ⟨subd12_3_1, List.forall_mem_cons.2 ⟨subd12_3_2, List.forall_mem_cons.2 ⟨subd12_3_3, List.forall_mem_cons.2 ⟨subd12_3_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd12_4 : ldCheck G d12_4.U d12_4.ms ldd12_4 = true := by decide +kernel
theorem pre_okd12_4 : subPre G cell12 d12_4 = true := by decide +kernel
theorem subd12_4_0 : subd12_4 [-1, -2] = true := by decide +kernel
theorem subd12_4_1 : subd12_4 [-1, -1] = true := by decide +kernel
theorem subd12_4_2 : subd12_4 [-1, 0] = true := by decide +kernel
theorem subd12_4_3 : subd12_4 [-1, 1] = true := by decide +kernel
theorem subd12_4_4 : subd12_4 [0, -2] = true := by decide +kernel
theorem subd12_4_5 : subd12_4 [0, -1] = true := by decide +kernel
theorem subd12_4_6 : subd12_4 [0, 0, -8] = true := by decide +kernel
theorem subd12_4_7 : subd12_4 [0, 0, -7] = true := by decide +kernel
theorem subd12_4_8 : subd12_4 [0, 0, -6] = true := by decide +kernel
theorem subd12_4_9 : subd12_4 [0, 0, -5] = true := by decide +kernel
theorem subd12_4_10 : subd12_4 [0, 0, -4] = true := by decide +kernel
theorem subd12_4_11 : subd12_4 [0, 0, -3] = true := by decide +kernel
theorem subd12_4_12 : subd12_4 [0, 0, -2] = true := by decide +kernel
theorem subd12_4_13 : subd12_4 [0, 0, -1] = true := by decide +kernel
theorem subd12_4_14 : subd12_4 [0, 0, 0] = true := by decide +kernel
theorem subd12_4_15 : subd12_4 [0, 0, 1] = true := by decide +kernel
theorem subd12_4_16 : subd12_4 [0, 0, 2] = true := by decide +kernel
theorem subd12_4_17 : subd12_4 [0, 0, 3] = true := by decide +kernel
theorem subd12_4_18 : subd12_4 [0, 0, 4] = true := by decide +kernel
theorem subd12_4_19 : subd12_4 [0, 0, 5] = true := by decide +kernel
theorem subd12_4_20 : subd12_4 [0, 0, 6] = true := by decide +kernel
theorem subd12_4_21 : subd12_4 [0, 0, 7] = true := by decide +kernel
theorem subd12_4_22 : subd12_4 [0, 1] = true := by decide +kernel
theorem subd12_4_23 : subd12_4 [1, -2] = true := by decide +kernel
theorem subd12_4_24 : subd12_4 [1, -1] = true := by decide +kernel
theorem subd12_4_25 : subd12_4 [1, 0] = true := by decide +kernel
theorem subd12_4_26 : subd12_4 [1, 1] = true := by decide +kernel
theorem sbd12_4_0 : ∀ q ∈ blkd12_4_0, subd12_4 q = true := by
  unfold blkd12_4_0
  exact List.forall_mem_cons.2 ⟨subd12_4_0, List.forall_mem_cons.2 ⟨subd12_4_1, List.forall_mem_cons.2 ⟨subd12_4_2, List.forall_mem_cons.2 ⟨subd12_4_3, List.forall_mem_cons.2 ⟨subd12_4_4, List.forall_mem_cons.2 ⟨subd12_4_5, List.forall_mem_cons.2 ⟨subd12_4_6, List.forall_mem_cons.2 ⟨subd12_4_7, List.forall_mem_cons.2 ⟨subd12_4_8, List.forall_mem_cons.2 ⟨subd12_4_9, List.forall_mem_cons.2 ⟨subd12_4_10, List.forall_mem_cons.2 ⟨subd12_4_11, List.forall_mem_cons.2 ⟨subd12_4_12, List.forall_mem_cons.2 ⟨subd12_4_13, List.forall_mem_cons.2 ⟨subd12_4_14, List.forall_mem_cons.2 ⟨subd12_4_15, List.forall_mem_cons.2 ⟨subd12_4_16, List.forall_mem_cons.2 ⟨subd12_4_17, List.forall_mem_cons.2 ⟨subd12_4_18, List.forall_mem_cons.2 ⟨subd12_4_19, List.forall_mem_cons.2 ⟨subd12_4_20, List.forall_mem_cons.2 ⟨subd12_4_21, List.forall_mem_cons.2 ⟨subd12_4_22, List.forall_mem_cons.2 ⟨subd12_4_23, List.forall_mem_cons.2 ⟨subd12_4_24, List.forall_mem_cons.2 ⟨subd12_4_25, List.forall_mem_cons.2 ⟨subd12_4_26, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd13_0 : ldCheck G d13_0.U d13_0.ms ldd13_0 = true := by decide +kernel
theorem pre_okd13_0 : subPre G cell13 d13_0 = true := by decide +kernel
theorem subd13_0_0 : subd13_0 [-1] = true := by decide +kernel
theorem subd13_0_1 : subd13_0 [0] = true := by decide +kernel
theorem subd13_0_2 : subd13_0 [1] = true := by decide +kernel
theorem sbd13_0_0 : ∀ q ∈ blkd13_0_0, subd13_0 q = true := by
  unfold blkd13_0_0
  exact List.forall_mem_cons.2 ⟨subd13_0_0, List.forall_mem_cons.2 ⟨subd13_0_1, List.forall_mem_cons.2 ⟨subd13_0_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd13_1 : ldCheck G d13_1.U d13_1.ms ldd13_1 = true := by decide +kernel
theorem pre_okd13_1 : subPre G cell13 d13_1 = true := by decide +kernel
theorem subd13_1_0 : subd13_1 [] = true := by decide +kernel
theorem sbd13_1_0 : ∀ q ∈ blkd13_1_0, subd13_1 q = true := by
  unfold blkd13_1_0
  exact List.forall_mem_cons.2 ⟨subd13_1_0, List.forall_mem_nil _⟩
theorem ld_okd13_2 : ldCheck G d13_2.U d13_2.ms ldd13_2 = true := by decide +kernel
theorem pre_okd13_2 : subPre G cell13 d13_2 = true := by decide +kernel
theorem subd13_2_0 : subd13_2 [-1] = true := by decide +kernel
theorem subd13_2_1 : subd13_2 [0, -2] = true := by decide +kernel
theorem subd13_2_2 : subd13_2 [0, -1] = true := by decide +kernel
theorem subd13_2_3 : subd13_2 [0, 0, -8] = true := by decide +kernel
theorem subd13_2_4 : subd13_2 [0, 0, -7] = true := by decide +kernel
theorem subd13_2_5 : subd13_2 [0, 0, -6] = true := by decide +kernel
theorem subd13_2_6 : subd13_2 [0, 0, -5] = true := by decide +kernel
theorem subd13_2_7 : subd13_2 [0, 0, -4] = true := by decide +kernel
theorem subd13_2_8 : subd13_2 [0, 0, -3] = true := by decide +kernel
theorem subd13_2_9 : subd13_2 [0, 0, -2] = true := by decide +kernel
theorem subd13_2_10 : subd13_2 [0, 0, -1] = true := by decide +kernel
theorem subd13_2_11 : subd13_2 [0, 0, 0] = true := by decide +kernel
theorem subd13_2_12 : subd13_2 [0, 0, 1] = true := by decide +kernel
theorem subd13_2_13 : subd13_2 [0, 0, 2] = true := by decide +kernel
theorem subd13_2_14 : subd13_2 [0, 0, 3] = true := by decide +kernel
theorem subd13_2_15 : subd13_2 [0, 0, 4] = true := by decide +kernel
theorem subd13_2_16 : subd13_2 [0, 0, 5] = true := by decide +kernel
theorem subd13_2_17 : subd13_2 [0, 0, 6] = true := by decide +kernel
theorem subd13_2_18 : subd13_2 [0, 0, 7] = true := by decide +kernel
theorem subd13_2_19 : subd13_2 [0, 1] = true := by decide +kernel
theorem subd13_2_20 : subd13_2 [1] = true := by decide +kernel
theorem sbd13_2_0 : ∀ q ∈ blkd13_2_0, subd13_2 q = true := by
  unfold blkd13_2_0
  exact List.forall_mem_cons.2 ⟨subd13_2_0, List.forall_mem_cons.2 ⟨subd13_2_1, List.forall_mem_cons.2 ⟨subd13_2_2, List.forall_mem_cons.2 ⟨subd13_2_3, List.forall_mem_cons.2 ⟨subd13_2_4, List.forall_mem_cons.2 ⟨subd13_2_5, List.forall_mem_cons.2 ⟨subd13_2_6, List.forall_mem_cons.2 ⟨subd13_2_7, List.forall_mem_cons.2 ⟨subd13_2_8, List.forall_mem_cons.2 ⟨subd13_2_9, List.forall_mem_cons.2 ⟨subd13_2_10, List.forall_mem_cons.2 ⟨subd13_2_11, List.forall_mem_cons.2 ⟨subd13_2_12, List.forall_mem_cons.2 ⟨subd13_2_13, List.forall_mem_cons.2 ⟨subd13_2_14, List.forall_mem_cons.2 ⟨subd13_2_15, List.forall_mem_cons.2 ⟨subd13_2_16, List.forall_mem_cons.2 ⟨subd13_2_17, List.forall_mem_cons.2 ⟨subd13_2_18, List.forall_mem_cons.2 ⟨subd13_2_19, List.forall_mem_cons.2 ⟨subd13_2_20, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C110
