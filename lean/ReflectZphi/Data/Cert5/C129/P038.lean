import ReflectZphi.Data.Cert5.C129.Base

namespace ReflectZphi.Data.Cert5.C129

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd12_0_0 : subd12_0 [-3] = true := by decide +kernel
theorem subd12_0_1 : subd12_0 [-2] = true := by decide +kernel
theorem subd12_0_2 : subd12_0 [-1, -4] = true := by decide +kernel
theorem subd12_0_3 : subd12_0 [-1, -3] = true := by decide +kernel
theorem subd12_0_4 : subd12_0 [-1, -2] = true := by decide +kernel
theorem subd12_0_5 : subd12_0 [-1, -1] = true := by decide +kernel
theorem subd12_0_6 : subd12_0 [-1, 0] = true := by decide +kernel
theorem subd12_0_7 : subd12_0 [-1, 1] = true := by decide +kernel
theorem subd12_0_8 : subd12_0 [-1, 2] = true := by decide +kernel
theorem subd12_0_9 : subd12_0 [-1, 3] = true := by decide +kernel
theorem subd12_0_10 : subd12_0 [0, -4] = true := by decide +kernel
theorem subd12_0_11 : subd12_0 [0, -3] = true := by decide +kernel
theorem subd12_0_12 : subd12_0 [0, -2] = true := by decide +kernel
theorem subd12_0_13 : subd12_0 [0, -1] = true := by decide +kernel
theorem subd12_0_14 : subd12_0 [0, 0] = true := by decide +kernel
theorem subd12_0_15 : subd12_0 [0, 1] = true := by decide +kernel
theorem subd12_0_16 : subd12_0 [0, 2] = true := by decide +kernel
theorem subd12_0_17 : subd12_0 [0, 3] = true := by decide +kernel
theorem subd12_0_18 : subd12_0 [1, -4] = true := by decide +kernel
theorem subd12_0_19 : subd12_0 [1, -3] = true := by decide +kernel
theorem subd12_0_20 : subd12_0 [1, -2] = true := by decide +kernel
theorem subd12_0_21 : subd12_0 [1, -1] = true := by decide +kernel
theorem subd12_0_22 : subd12_0 [1, 0] = true := by decide +kernel
theorem subd12_0_23 : subd12_0 [1, 1] = true := by decide +kernel
theorem subd12_0_24 : subd12_0 [1, 2] = true := by decide +kernel
theorem subd12_0_25 : subd12_0 [1, 3] = true := by decide +kernel
theorem subd12_0_26 : subd12_0 [2] = true := by decide +kernel
theorem subd12_0_27 : subd12_0 [3] = true := by decide +kernel
theorem sbd12_0_0 : ∀ q ∈ blkd12_0_0, subd12_0 q = true := by
  unfold blkd12_0_0
  exact List.forall_mem_cons.2 ⟨subd12_0_0, List.forall_mem_cons.2 ⟨subd12_0_1, List.forall_mem_cons.2 ⟨subd12_0_2, List.forall_mem_cons.2 ⟨subd12_0_3, List.forall_mem_cons.2 ⟨subd12_0_4, List.forall_mem_cons.2 ⟨subd12_0_5, List.forall_mem_cons.2 ⟨subd12_0_6, List.forall_mem_cons.2 ⟨subd12_0_7, List.forall_mem_cons.2 ⟨subd12_0_8, List.forall_mem_cons.2 ⟨subd12_0_9, List.forall_mem_cons.2 ⟨subd12_0_10, List.forall_mem_cons.2 ⟨subd12_0_11, List.forall_mem_cons.2 ⟨subd12_0_12, List.forall_mem_cons.2 ⟨subd12_0_13, List.forall_mem_cons.2 ⟨subd12_0_14, List.forall_mem_cons.2 ⟨subd12_0_15, List.forall_mem_cons.2 ⟨subd12_0_16, List.forall_mem_cons.2 ⟨subd12_0_17, List.forall_mem_cons.2 ⟨subd12_0_18, List.forall_mem_cons.2 ⟨subd12_0_19, List.forall_mem_cons.2 ⟨subd12_0_20, List.forall_mem_cons.2 ⟨subd12_0_21, List.forall_mem_cons.2 ⟨subd12_0_22, List.forall_mem_cons.2 ⟨subd12_0_23, List.forall_mem_cons.2 ⟨subd12_0_24, List.forall_mem_cons.2 ⟨subd12_0_25, List.forall_mem_cons.2 ⟨subd12_0_26, List.forall_mem_cons.2 ⟨subd12_0_27, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd12_1 : ldCheck G d12_1.U d12_1.ms ldd12_1 = true := by decide +kernel
theorem pre_okd12_1 : subPre G cell12 d12_1 = true := by decide +kernel
theorem subd12_1_0 : subd12_1 [-3] = true := by decide +kernel
theorem subd12_1_1 : subd12_1 [-2] = true := by decide +kernel
theorem subd12_1_2 : subd12_1 [-1, -4] = true := by decide +kernel
theorem subd12_1_3 : subd12_1 [-1, -3] = true := by decide +kernel
theorem subd12_1_4 : subd12_1 [-1, -2] = true := by decide +kernel
theorem subd12_1_5 : subd12_1 [-1, -1] = true := by decide +kernel
theorem subd12_1_6 : subd12_1 [-1, 0] = true := by decide +kernel
theorem subd12_1_7 : subd12_1 [-1, 1] = true := by decide +kernel
theorem subd12_1_8 : subd12_1 [-1, 2] = true := by decide +kernel
theorem subd12_1_9 : subd12_1 [-1, 3] = true := by decide +kernel
theorem subd12_1_10 : subd12_1 [0, -4] = true := by decide +kernel
theorem subd12_1_11 : subd12_1 [0, -3] = true := by decide +kernel
theorem subd12_1_12 : subd12_1 [0, -2] = true := by decide +kernel
theorem subd12_1_13 : subd12_1 [0, -1] = true := by decide +kernel
theorem subd12_1_14 : subd12_1 [0, 0] = true := by decide +kernel
theorem subd12_1_15 : subd12_1 [0, 1] = true := by decide +kernel
theorem subd12_1_16 : subd12_1 [0, 2] = true := by decide +kernel
theorem subd12_1_17 : subd12_1 [0, 3] = true := by decide +kernel
theorem subd12_1_18 : subd12_1 [1, -4] = true := by decide +kernel
theorem subd12_1_19 : subd12_1 [1, -3] = true := by decide +kernel
theorem subd12_1_20 : subd12_1 [1, -2] = true := by decide +kernel
theorem subd12_1_21 : subd12_1 [1, -1] = true := by decide +kernel
theorem subd12_1_22 : subd12_1 [1, 0] = true := by decide +kernel
theorem subd12_1_23 : subd12_1 [1, 1] = true := by decide +kernel
theorem subd12_1_24 : subd12_1 [1, 2] = true := by decide +kernel
theorem subd12_1_25 : subd12_1 [1, 3] = true := by decide +kernel
theorem subd12_1_26 : subd12_1 [2] = true := by decide +kernel
theorem subd12_1_27 : subd12_1 [3] = true := by decide +kernel
theorem sbd12_1_0 : ∀ q ∈ blkd12_1_0, subd12_1 q = true := by
  unfold blkd12_1_0
  exact List.forall_mem_cons.2 ⟨subd12_1_0, List.forall_mem_cons.2 ⟨subd12_1_1, List.forall_mem_cons.2 ⟨subd12_1_2, List.forall_mem_cons.2 ⟨subd12_1_3, List.forall_mem_cons.2 ⟨subd12_1_4, List.forall_mem_cons.2 ⟨subd12_1_5, List.forall_mem_cons.2 ⟨subd12_1_6, List.forall_mem_cons.2 ⟨subd12_1_7, List.forall_mem_cons.2 ⟨subd12_1_8, List.forall_mem_cons.2 ⟨subd12_1_9, List.forall_mem_cons.2 ⟨subd12_1_10, List.forall_mem_cons.2 ⟨subd12_1_11, List.forall_mem_cons.2 ⟨subd12_1_12, List.forall_mem_cons.2 ⟨subd12_1_13, List.forall_mem_cons.2 ⟨subd12_1_14, List.forall_mem_cons.2 ⟨subd12_1_15, List.forall_mem_cons.2 ⟨subd12_1_16, List.forall_mem_cons.2 ⟨subd12_1_17, List.forall_mem_cons.2 ⟨subd12_1_18, List.forall_mem_cons.2 ⟨subd12_1_19, List.forall_mem_cons.2 ⟨subd12_1_20, List.forall_mem_cons.2 ⟨subd12_1_21, List.forall_mem_cons.2 ⟨subd12_1_22, List.forall_mem_cons.2 ⟨subd12_1_23, List.forall_mem_cons.2 ⟨subd12_1_24, List.forall_mem_cons.2 ⟨subd12_1_25, List.forall_mem_cons.2 ⟨subd12_1_26, List.forall_mem_cons.2 ⟨subd12_1_27, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd12_2 : ldCheck G d12_2.U d12_2.ms ldd12_2 = true := by decide +kernel
theorem pre_okd12_2 : subPre G cell12 d12_2 = true := by decide +kernel
theorem subd12_2_0 : subd12_2 [-2] = true := by decide +kernel
theorem subd12_2_1 : subd12_2 [-1, -2] = true := by decide +kernel
theorem subd12_2_2 : subd12_2 [-1, -1] = true := by decide +kernel
theorem subd12_2_3 : subd12_2 [-1, 0] = true := by decide +kernel
theorem subd12_2_4 : subd12_2 [-1, 1] = true := by decide +kernel
theorem subd12_2_5 : subd12_2 [0, -3] = true := by decide +kernel
theorem subd12_2_6 : subd12_2 [0, -2] = true := by decide +kernel
theorem subd12_2_7 : subd12_2 [0, -1] = true := by decide +kernel
theorem subd12_2_8 : subd12_2 [0, 0] = true := by decide +kernel
theorem subd12_2_9 : subd12_2 [0, 1] = true := by decide +kernel
theorem subd12_2_10 : subd12_2 [0, 2] = true := by decide +kernel
theorem subd12_2_11 : subd12_2 [1, -2] = true := by decide +kernel
theorem subd12_2_12 : subd12_2 [1, -1] = true := by decide +kernel
theorem subd12_2_13 : subd12_2 [1, 0] = true := by decide +kernel
theorem subd12_2_14 : subd12_2 [1, 1] = true := by decide +kernel
theorem subd12_2_15 : subd12_2 [2] = true := by decide +kernel
theorem sbd12_2_0 : ∀ q ∈ blkd12_2_0, subd12_2 q = true := by
  unfold blkd12_2_0
  exact List.forall_mem_cons.2 ⟨subd12_2_0, List.forall_mem_cons.2 ⟨subd12_2_1, List.forall_mem_cons.2 ⟨subd12_2_2, List.forall_mem_cons.2 ⟨subd12_2_3, List.forall_mem_cons.2 ⟨subd12_2_4, List.forall_mem_cons.2 ⟨subd12_2_5, List.forall_mem_cons.2 ⟨subd12_2_6, List.forall_mem_cons.2 ⟨subd12_2_7, List.forall_mem_cons.2 ⟨subd12_2_8, List.forall_mem_cons.2 ⟨subd12_2_9, List.forall_mem_cons.2 ⟨subd12_2_10, List.forall_mem_cons.2 ⟨subd12_2_11, List.forall_mem_cons.2 ⟨subd12_2_12, List.forall_mem_cons.2 ⟨subd12_2_13, List.forall_mem_cons.2 ⟨subd12_2_14, List.forall_mem_cons.2 ⟨subd12_2_15, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd12_3 : ldCheck G d12_3.U d12_3.ms ldd12_3 = true := by decide +kernel
theorem pre_okd12_3 : subPre G cell12 d12_3 = true := by decide +kernel
theorem subd12_3_0 : subd12_3 [-3] = true := by decide +kernel
theorem subd12_3_1 : subd12_3 [-2] = true := by decide +kernel
theorem subd12_3_2 : subd12_3 [-1, -4] = true := by decide +kernel
theorem subd12_3_3 : subd12_3 [-1, -3] = true := by decide +kernel
theorem subd12_3_4 : subd12_3 [-1, -2] = true := by decide +kernel
theorem subd12_3_5 : subd12_3 [-1, -1] = true := by decide +kernel
theorem subd12_3_6 : subd12_3 [-1, 0] = true := by decide +kernel
theorem subd12_3_7 : subd12_3 [-1, 1] = true := by decide +kernel
theorem subd12_3_8 : subd12_3 [-1, 2] = true := by decide +kernel
theorem subd12_3_9 : subd12_3 [-1, 3] = true := by decide +kernel
theorem subd12_3_10 : subd12_3 [0, -4] = true := by decide +kernel
theorem subd12_3_11 : subd12_3 [0, -3] = true := by decide +kernel
theorem subd12_3_12 : subd12_3 [0, -2] = true := by decide +kernel
theorem subd12_3_13 : subd12_3 [0, -1] = true := by decide +kernel
theorem subd12_3_14 : subd12_3 [0, 0] = true := by decide +kernel
theorem subd12_3_15 : subd12_3 [0, 1] = true := by decide +kernel
theorem subd12_3_16 : subd12_3 [0, 2] = true := by decide +kernel
theorem subd12_3_17 : subd12_3 [0, 3] = true := by decide +kernel
theorem subd12_3_18 : subd12_3 [1, -4] = true := by decide +kernel
theorem subd12_3_19 : subd12_3 [1, -3] = true := by decide +kernel
theorem subd12_3_20 : subd12_3 [1, -2] = true := by decide +kernel
theorem subd12_3_21 : subd12_3 [1, -1] = true := by decide +kernel
theorem subd12_3_22 : subd12_3 [1, 0] = true := by decide +kernel
theorem subd12_3_23 : subd12_3 [1, 1] = true := by decide +kernel
theorem subd12_3_24 : subd12_3 [1, 2] = true := by decide +kernel
theorem subd12_3_25 : subd12_3 [1, 3] = true := by decide +kernel
theorem subd12_3_26 : subd12_3 [2] = true := by decide +kernel
theorem subd12_3_27 : subd12_3 [3] = true := by decide +kernel
theorem sbd12_3_0 : ∀ q ∈ blkd12_3_0, subd12_3 q = true := by
  unfold blkd12_3_0
  exact List.forall_mem_cons.2 ⟨subd12_3_0, List.forall_mem_cons.2 ⟨subd12_3_1, List.forall_mem_cons.2 ⟨subd12_3_2, List.forall_mem_cons.2 ⟨subd12_3_3, List.forall_mem_cons.2 ⟨subd12_3_4, List.forall_mem_cons.2 ⟨subd12_3_5, List.forall_mem_cons.2 ⟨subd12_3_6, List.forall_mem_cons.2 ⟨subd12_3_7, List.forall_mem_cons.2 ⟨subd12_3_8, List.forall_mem_cons.2 ⟨subd12_3_9, List.forall_mem_cons.2 ⟨subd12_3_10, List.forall_mem_cons.2 ⟨subd12_3_11, List.forall_mem_cons.2 ⟨subd12_3_12, List.forall_mem_cons.2 ⟨subd12_3_13, List.forall_mem_cons.2 ⟨subd12_3_14, List.forall_mem_cons.2 ⟨subd12_3_15, List.forall_mem_cons.2 ⟨subd12_3_16, List.forall_mem_cons.2 ⟨subd12_3_17, List.forall_mem_cons.2 ⟨subd12_3_18, List.forall_mem_cons.2 ⟨subd12_3_19, List.forall_mem_cons.2 ⟨subd12_3_20, List.forall_mem_cons.2 ⟨subd12_3_21, List.forall_mem_cons.2 ⟨subd12_3_22, List.forall_mem_cons.2 ⟨subd12_3_23, List.forall_mem_cons.2 ⟨subd12_3_24, List.forall_mem_cons.2 ⟨subd12_3_25, List.forall_mem_cons.2 ⟨subd12_3_26, List.forall_mem_cons.2 ⟨subd12_3_27, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd13_0 : ldCheck G d13_0.U d13_0.ms ldd13_0 = true := by decide +kernel
theorem pre_okd13_0 : subPre G cell13 d13_0 = true := by decide +kernel
theorem subd13_0_0 : subd13_0 [-2] = true := by decide +kernel
theorem subd13_0_1 : subd13_0 [-1] = true := by decide +kernel
theorem subd13_0_2 : subd13_0 [0, -3] = true := by decide +kernel
theorem subd13_0_3 : subd13_0 [0, -2] = true := by decide +kernel
theorem subd13_0_4 : subd13_0 [0, -1] = true := by decide +kernel
theorem subd13_0_5 : subd13_0 [0, 0] = true := by decide +kernel
theorem subd13_0_6 : subd13_0 [0, 1] = true := by decide +kernel
theorem subd13_0_7 : subd13_0 [0, 2] = true := by decide +kernel
theorem subd13_0_8 : subd13_0 [1] = true := by decide +kernel
theorem subd13_0_9 : subd13_0 [2] = true := by decide +kernel
theorem sbd13_0_0 : ∀ q ∈ blkd13_0_0, subd13_0 q = true := by
  unfold blkd13_0_0
  exact List.forall_mem_cons.2 ⟨subd13_0_0, List.forall_mem_cons.2 ⟨subd13_0_1, List.forall_mem_cons.2 ⟨subd13_0_2, List.forall_mem_cons.2 ⟨subd13_0_3, List.forall_mem_cons.2 ⟨subd13_0_4, List.forall_mem_cons.2 ⟨subd13_0_5, List.forall_mem_cons.2 ⟨subd13_0_6, List.forall_mem_cons.2 ⟨subd13_0_7, List.forall_mem_cons.2 ⟨subd13_0_8, List.forall_mem_cons.2 ⟨subd13_0_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd13_1 : ldCheck G d13_1.U d13_1.ms ldd13_1 = true := by decide +kernel
theorem pre_okd13_1 : subPre G cell13 d13_1 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C129
