import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd31_0 : ldCheck G d31_0.U d31_0.ms ldd31_0 = true := by decide +kernel
theorem pre_okd31_0 : subPre G cell31 d31_0 = true := by decide +kernel
theorem subd31_0_0 : subd31_0 [-1, -2] = true := by decide +kernel
theorem subd31_0_1 : subd31_0 [-1, -1] = true := by decide +kernel
theorem subd31_0_2 : subd31_0 [-1, 0] = true := by decide +kernel
theorem subd31_0_3 : subd31_0 [-1, 1] = true := by decide +kernel
theorem subd31_0_4 : subd31_0 [-1, 2] = true := by decide +kernel
theorem subd31_0_5 : subd31_0 [0, -3] = true := by decide +kernel
theorem subd31_0_6 : subd31_0 [0, -2] = true := by decide +kernel
theorem subd31_0_7 : subd31_0 [0, -1] = true := by decide +kernel
theorem subd31_0_8 : subd31_0 [0, 0] = true := by decide +kernel
theorem subd31_0_9 : subd31_0 [0, 1] = true := by decide +kernel
theorem subd31_0_10 : subd31_0 [0, 2] = true := by decide +kernel
theorem subd31_0_11 : subd31_0 [1, -3] = true := by decide +kernel
theorem subd31_0_12 : subd31_0 [1, -2] = true := by decide +kernel
theorem subd31_0_13 : subd31_0 [1, -1] = true := by decide +kernel
theorem subd31_0_14 : subd31_0 [1, 0] = true := by decide +kernel
theorem subd31_0_15 : subd31_0 [1, 1] = true := by decide +kernel
theorem sbd31_0_0 : ∀ q ∈ blkd31_0_0, subd31_0 q = true := by
  unfold blkd31_0_0
  exact List.forall_mem_cons.2 ⟨subd31_0_0, List.forall_mem_cons.2 ⟨subd31_0_1, List.forall_mem_cons.2 ⟨subd31_0_2, List.forall_mem_cons.2 ⟨subd31_0_3, List.forall_mem_cons.2 ⟨subd31_0_4, List.forall_mem_cons.2 ⟨subd31_0_5, List.forall_mem_cons.2 ⟨subd31_0_6, List.forall_mem_cons.2 ⟨subd31_0_7, List.forall_mem_cons.2 ⟨subd31_0_8, List.forall_mem_cons.2 ⟨subd31_0_9, List.forall_mem_cons.2 ⟨subd31_0_10, List.forall_mem_cons.2 ⟨subd31_0_11, List.forall_mem_cons.2 ⟨subd31_0_12, List.forall_mem_cons.2 ⟨subd31_0_13, List.forall_mem_cons.2 ⟨subd31_0_14, List.forall_mem_cons.2 ⟨subd31_0_15, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd31_1 : ldCheck G d31_1.U d31_1.ms ldd31_1 = true := by decide +kernel
theorem pre_okd31_1 : subPre G cell31 d31_1 = true := by decide +kernel
theorem subd31_1_0 : subd31_1 [-3] = true := by decide +kernel
theorem subd31_1_1 : subd31_1 [-2] = true := by decide +kernel
theorem subd31_1_2 : subd31_1 [-1, -4] = true := by decide +kernel
theorem subd31_1_3 : subd31_1 [-1, -3] = true := by decide +kernel
theorem subd31_1_4 : subd31_1 [-1, -2] = true := by decide +kernel
theorem subd31_1_5 : subd31_1 [-1, -1] = true := by decide +kernel
theorem subd31_1_6 : subd31_1 [-1, 0] = true := by decide +kernel
theorem subd31_1_7 : subd31_1 [-1, 1] = true := by decide +kernel
theorem subd31_1_8 : subd31_1 [-1, 2] = true := by decide +kernel
theorem subd31_1_9 : subd31_1 [-1, 3] = true := by decide +kernel
theorem subd31_1_10 : subd31_1 [0, -4] = true := by decide +kernel
theorem subd31_1_11 : subd31_1 [0, -3] = true := by decide +kernel
theorem subd31_1_12 : subd31_1 [0, -2] = true := by decide +kernel
theorem subd31_1_13 : subd31_1 [0, -1] = true := by decide +kernel
theorem subd31_1_14 : subd31_1 [0, 0] = true := by decide +kernel
theorem subd31_1_15 : subd31_1 [0, 1] = true := by decide +kernel
theorem subd31_1_16 : subd31_1 [0, 2] = true := by decide +kernel
theorem subd31_1_17 : subd31_1 [0, 3] = true := by decide +kernel
theorem subd31_1_18 : subd31_1 [1, -4] = true := by decide +kernel
theorem subd31_1_19 : subd31_1 [1, -3] = true := by decide +kernel
theorem subd31_1_20 : subd31_1 [1, -2] = true := by decide +kernel
theorem subd31_1_21 : subd31_1 [1, -1] = true := by decide +kernel
theorem subd31_1_22 : subd31_1 [1, 0] = true := by decide +kernel
theorem subd31_1_23 : subd31_1 [1, 1] = true := by decide +kernel
theorem subd31_1_24 : subd31_1 [1, 2] = true := by decide +kernel
theorem subd31_1_25 : subd31_1 [1, 3] = true := by decide +kernel
theorem subd31_1_26 : subd31_1 [2] = true := by decide +kernel
theorem subd31_1_27 : subd31_1 [3] = true := by decide +kernel
theorem sbd31_1_0 : ∀ q ∈ blkd31_1_0, subd31_1 q = true := by
  unfold blkd31_1_0
  exact List.forall_mem_cons.2 ⟨subd31_1_0, List.forall_mem_cons.2 ⟨subd31_1_1, List.forall_mem_cons.2 ⟨subd31_1_2, List.forall_mem_cons.2 ⟨subd31_1_3, List.forall_mem_cons.2 ⟨subd31_1_4, List.forall_mem_cons.2 ⟨subd31_1_5, List.forall_mem_cons.2 ⟨subd31_1_6, List.forall_mem_cons.2 ⟨subd31_1_7, List.forall_mem_cons.2 ⟨subd31_1_8, List.forall_mem_cons.2 ⟨subd31_1_9, List.forall_mem_cons.2 ⟨subd31_1_10, List.forall_mem_cons.2 ⟨subd31_1_11, List.forall_mem_cons.2 ⟨subd31_1_12, List.forall_mem_cons.2 ⟨subd31_1_13, List.forall_mem_cons.2 ⟨subd31_1_14, List.forall_mem_cons.2 ⟨subd31_1_15, List.forall_mem_cons.2 ⟨subd31_1_16, List.forall_mem_cons.2 ⟨subd31_1_17, List.forall_mem_cons.2 ⟨subd31_1_18, List.forall_mem_cons.2 ⟨subd31_1_19, List.forall_mem_cons.2 ⟨subd31_1_20, List.forall_mem_cons.2 ⟨subd31_1_21, List.forall_mem_cons.2 ⟨subd31_1_22, List.forall_mem_cons.2 ⟨subd31_1_23, List.forall_mem_cons.2 ⟨subd31_1_24, List.forall_mem_cons.2 ⟨subd31_1_25, List.forall_mem_cons.2 ⟨subd31_1_26, List.forall_mem_cons.2 ⟨subd31_1_27, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd31_2 : ldCheck G d31_2.U d31_2.ms ldd31_2 = true := by decide +kernel
theorem pre_okd31_2 : subPre G cell31 d31_2 = true := by decide +kernel
theorem subd31_2_0 : subd31_2 [-3] = true := by decide +kernel
theorem subd31_2_1 : subd31_2 [-2] = true := by decide +kernel
theorem subd31_2_2 : subd31_2 [-1, -4] = true := by decide +kernel
theorem subd31_2_3 : subd31_2 [-1, -3] = true := by decide +kernel
theorem subd31_2_4 : subd31_2 [-1, -2] = true := by decide +kernel
theorem subd31_2_5 : subd31_2 [-1, -1] = true := by decide +kernel
theorem subd31_2_6 : subd31_2 [-1, 0] = true := by decide +kernel
theorem subd31_2_7 : subd31_2 [-1, 1] = true := by decide +kernel
theorem subd31_2_8 : subd31_2 [-1, 2] = true := by decide +kernel
theorem subd31_2_9 : subd31_2 [0, -4] = true := by decide +kernel
theorem subd31_2_10 : subd31_2 [0, -3] = true := by decide +kernel
theorem subd31_2_11 : subd31_2 [0, -2] = true := by decide +kernel
theorem subd31_2_12 : subd31_2 [0, -1] = true := by decide +kernel
theorem subd31_2_13 : subd31_2 [0, 0] = true := by decide +kernel
theorem subd31_2_14 : subd31_2 [0, 1] = true := by decide +kernel
theorem subd31_2_15 : subd31_2 [0, 2] = true := by decide +kernel
theorem subd31_2_16 : subd31_2 [0, 3] = true := by decide +kernel
theorem subd31_2_17 : subd31_2 [1, -3] = true := by decide +kernel
theorem subd31_2_18 : subd31_2 [1, -2] = true := by decide +kernel
theorem subd31_2_19 : subd31_2 [1, -1] = true := by decide +kernel
theorem subd31_2_20 : subd31_2 [1, 0] = true := by decide +kernel
theorem subd31_2_21 : subd31_2 [1, 1] = true := by decide +kernel
theorem subd31_2_22 : subd31_2 [1, 2] = true := by decide +kernel
theorem subd31_2_23 : subd31_2 [1, 3] = true := by decide +kernel
theorem subd31_2_24 : subd31_2 [2] = true := by decide +kernel
theorem subd31_2_25 : subd31_2 [3] = true := by decide +kernel
theorem sbd31_2_0 : ∀ q ∈ blkd31_2_0, subd31_2 q = true := by
  unfold blkd31_2_0
  exact List.forall_mem_cons.2 ⟨subd31_2_0, List.forall_mem_cons.2 ⟨subd31_2_1, List.forall_mem_cons.2 ⟨subd31_2_2, List.forall_mem_cons.2 ⟨subd31_2_3, List.forall_mem_cons.2 ⟨subd31_2_4, List.forall_mem_cons.2 ⟨subd31_2_5, List.forall_mem_cons.2 ⟨subd31_2_6, List.forall_mem_cons.2 ⟨subd31_2_7, List.forall_mem_cons.2 ⟨subd31_2_8, List.forall_mem_cons.2 ⟨subd31_2_9, List.forall_mem_cons.2 ⟨subd31_2_10, List.forall_mem_cons.2 ⟨subd31_2_11, List.forall_mem_cons.2 ⟨subd31_2_12, List.forall_mem_cons.2 ⟨subd31_2_13, List.forall_mem_cons.2 ⟨subd31_2_14, List.forall_mem_cons.2 ⟨subd31_2_15, List.forall_mem_cons.2 ⟨subd31_2_16, List.forall_mem_cons.2 ⟨subd31_2_17, List.forall_mem_cons.2 ⟨subd31_2_18, List.forall_mem_cons.2 ⟨subd31_2_19, List.forall_mem_cons.2 ⟨subd31_2_20, List.forall_mem_cons.2 ⟨subd31_2_21, List.forall_mem_cons.2 ⟨subd31_2_22, List.forall_mem_cons.2 ⟨subd31_2_23, List.forall_mem_cons.2 ⟨subd31_2_24, List.forall_mem_cons.2 ⟨subd31_2_25, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd31_3 : ldCheck G d31_3.U d31_3.ms ldd31_3 = true := by decide +kernel
theorem pre_okd31_3 : subPre G cell31 d31_3 = true := by decide +kernel
theorem subd31_3_0 : subd31_3 [-3] = true := by decide +kernel
theorem subd31_3_1 : subd31_3 [-2] = true := by decide +kernel
theorem subd31_3_2 : subd31_3 [-1, -4] = true := by decide +kernel
theorem subd31_3_3 : subd31_3 [-1, -3] = true := by decide +kernel
theorem subd31_3_4 : subd31_3 [-1, -2] = true := by decide +kernel
theorem subd31_3_5 : subd31_3 [-1, -1] = true := by decide +kernel
theorem subd31_3_6 : subd31_3 [-1, 0] = true := by decide +kernel
theorem subd31_3_7 : subd31_3 [-1, 1] = true := by decide +kernel
theorem subd31_3_8 : subd31_3 [-1, 2] = true := by decide +kernel
theorem subd31_3_9 : subd31_3 [-1, 3] = true := by decide +kernel
theorem subd31_3_10 : subd31_3 [0, -4] = true := by decide +kernel
theorem subd31_3_11 : subd31_3 [0, -3] = true := by decide +kernel
theorem subd31_3_12 : subd31_3 [0, -2] = true := by decide +kernel
theorem subd31_3_13 : subd31_3 [0, -1] = true := by decide +kernel
theorem subd31_3_14 : subd31_3 [0, 0] = true := by decide +kernel
theorem subd31_3_15 : subd31_3 [0, 1] = true := by decide +kernel
theorem subd31_3_16 : subd31_3 [0, 2] = true := by decide +kernel
theorem subd31_3_17 : subd31_3 [0, 3] = true := by decide +kernel
theorem subd31_3_18 : subd31_3 [1, -4] = true := by decide +kernel
theorem subd31_3_19 : subd31_3 [1, -3] = true := by decide +kernel
theorem subd31_3_20 : subd31_3 [1, -2] = true := by decide +kernel
theorem subd31_3_21 : subd31_3 [1, -1] = true := by decide +kernel
theorem subd31_3_22 : subd31_3 [1, 0] = true := by decide +kernel
theorem subd31_3_23 : subd31_3 [1, 1] = true := by decide +kernel
theorem subd31_3_24 : subd31_3 [1, 2] = true := by decide +kernel
theorem subd31_3_25 : subd31_3 [1, 3] = true := by decide +kernel
theorem subd31_3_26 : subd31_3 [2] = true := by decide +kernel
theorem subd31_3_27 : subd31_3 [3] = true := by decide +kernel
theorem sbd31_3_0 : ∀ q ∈ blkd31_3_0, subd31_3 q = true := by
  unfold blkd31_3_0
  exact List.forall_mem_cons.2 ⟨subd31_3_0, List.forall_mem_cons.2 ⟨subd31_3_1, List.forall_mem_cons.2 ⟨subd31_3_2, List.forall_mem_cons.2 ⟨subd31_3_3, List.forall_mem_cons.2 ⟨subd31_3_4, List.forall_mem_cons.2 ⟨subd31_3_5, List.forall_mem_cons.2 ⟨subd31_3_6, List.forall_mem_cons.2 ⟨subd31_3_7, List.forall_mem_cons.2 ⟨subd31_3_8, List.forall_mem_cons.2 ⟨subd31_3_9, List.forall_mem_cons.2 ⟨subd31_3_10, List.forall_mem_cons.2 ⟨subd31_3_11, List.forall_mem_cons.2 ⟨subd31_3_12, List.forall_mem_cons.2 ⟨subd31_3_13, List.forall_mem_cons.2 ⟨subd31_3_14, List.forall_mem_cons.2 ⟨subd31_3_15, List.forall_mem_cons.2 ⟨subd31_3_16, List.forall_mem_cons.2 ⟨subd31_3_17, List.forall_mem_cons.2 ⟨subd31_3_18, List.forall_mem_cons.2 ⟨subd31_3_19, List.forall_mem_cons.2 ⟨subd31_3_20, List.forall_mem_cons.2 ⟨subd31_3_21, List.forall_mem_cons.2 ⟨subd31_3_22, List.forall_mem_cons.2 ⟨subd31_3_23, List.forall_mem_cons.2 ⟨subd31_3_24, List.forall_mem_cons.2 ⟨subd31_3_25, List.forall_mem_cons.2 ⟨subd31_3_26, List.forall_mem_cons.2 ⟨subd31_3_27, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd32_0 : ldCheck G d32_0.U d32_0.ms ldd32_0 = true := by decide +kernel
theorem pre_okd32_0 : subPre G cell32 d32_0 = true := by decide +kernel
theorem subd32_0_0 : subd32_0 [-2] = true := by decide +kernel
theorem subd32_0_1 : subd32_0 [-1] = true := by decide +kernel
theorem subd32_0_2 : subd32_0 [0] = true := by decide +kernel
theorem subd32_0_3 : subd32_0 [1] = true := by decide +kernel
theorem subd32_0_4 : subd32_0 [2] = true := by decide +kernel
theorem sbd32_0_0 : ∀ q ∈ blkd32_0_0, subd32_0 q = true := by
  unfold blkd32_0_0
  exact List.forall_mem_cons.2 ⟨subd32_0_0, List.forall_mem_cons.2 ⟨subd32_0_1, List.forall_mem_cons.2 ⟨subd32_0_2, List.forall_mem_cons.2 ⟨subd32_0_3, List.forall_mem_cons.2 ⟨subd32_0_4, List.forall_mem_nil _⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
