import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd2_5_0 : subd2_5 [-3] = true := by decide +kernel
theorem subd2_5_1 : subd2_5 [-2] = true := by decide +kernel
theorem subd2_5_2 : subd2_5 [-1] = true := by decide +kernel
theorem subd2_5_3 : subd2_5 [0, -3] = true := by decide +kernel
theorem subd2_5_4 : subd2_5 [0, -2] = true := by decide +kernel
theorem subd2_5_5 : subd2_5 [0, -1] = true := by decide +kernel
theorem subd2_5_6 : subd2_5 [0, 0] = true := by decide +kernel
theorem subd2_5_7 : subd2_5 [0, 1] = true := by decide +kernel
theorem subd2_5_8 : subd2_5 [0, 2] = true := by decide +kernel
theorem subd2_5_9 : subd2_5 [1] = true := by decide +kernel
theorem subd2_5_10 : subd2_5 [2] = true := by decide +kernel
theorem subd2_5_11 : subd2_5 [3] = true := by decide +kernel
theorem sbd2_5_0 : ∀ q ∈ blkd2_5_0, subd2_5 q = true := by
  unfold blkd2_5_0
  exact List.forall_mem_cons.2 ⟨subd2_5_0, List.forall_mem_cons.2 ⟨subd2_5_1, List.forall_mem_cons.2 ⟨subd2_5_2, List.forall_mem_cons.2 ⟨subd2_5_3, List.forall_mem_cons.2 ⟨subd2_5_4, List.forall_mem_cons.2 ⟨subd2_5_5, List.forall_mem_cons.2 ⟨subd2_5_6, List.forall_mem_cons.2 ⟨subd2_5_7, List.forall_mem_cons.2 ⟨subd2_5_8, List.forall_mem_cons.2 ⟨subd2_5_9, List.forall_mem_cons.2 ⟨subd2_5_10, List.forall_mem_cons.2 ⟨subd2_5_11, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd2_6 : ldCheck G d2_6.U d2_6.ms ldd2_6 = true := by decide +kernel
theorem pre_okd2_6 : subPre G cell2 d2_6 = true := by decide +kernel
theorem subd2_6_0 : subd2_6 [-1] = true := by decide +kernel
theorem subd2_6_1 : subd2_6 [0, -2] = true := by decide +kernel
theorem subd2_6_2 : subd2_6 [0, -1] = true := by decide +kernel
theorem subd2_6_3 : subd2_6 [0, 0, -10] = true := by decide +kernel
theorem subd2_6_4 : subd2_6 [0, 0, -9] = true := by decide +kernel
theorem subd2_6_5 : subd2_6 [0, 0, -8] = true := by decide +kernel
theorem subd2_6_6 : subd2_6 [0, 0, -7] = true := by decide +kernel
theorem subd2_6_7 : subd2_6 [0, 0, -6] = true := by decide +kernel
theorem subd2_6_8 : subd2_6 [0, 0, -5] = true := by decide +kernel
theorem subd2_6_9 : subd2_6 [0, 0, -4] = true := by decide +kernel
theorem subd2_6_10 : subd2_6 [0, 0, -3] = true := by decide +kernel
theorem subd2_6_11 : subd2_6 [0, 0, -2] = true := by decide +kernel
theorem subd2_6_12 : subd2_6 [0, 0, -1] = true := by decide +kernel
theorem subd2_6_13 : subd2_6 [0, 0, 0] = true := by decide +kernel
theorem subd2_6_14 : subd2_6 [0, 0, 1] = true := by decide +kernel
theorem subd2_6_15 : subd2_6 [0, 0, 2] = true := by decide +kernel
theorem subd2_6_16 : subd2_6 [0, 0, 3] = true := by decide +kernel
theorem subd2_6_17 : subd2_6 [0, 0, 4] = true := by decide +kernel
theorem subd2_6_18 : subd2_6 [0, 0, 5] = true := by decide +kernel
theorem subd2_6_19 : subd2_6 [0, 0, 6] = true := by decide +kernel
theorem subd2_6_20 : subd2_6 [0, 0, 7] = true := by decide +kernel
theorem subd2_6_21 : subd2_6 [0, 0, 8] = true := by decide +kernel
theorem subd2_6_22 : subd2_6 [0, 0, 9] = true := by decide +kernel
theorem subd2_6_23 : subd2_6 [0, 1] = true := by decide +kernel
theorem subd2_6_24 : subd2_6 [1] = true := by decide +kernel
theorem sbd2_6_0 : ∀ q ∈ blkd2_6_0, subd2_6 q = true := by
  unfold blkd2_6_0
  exact List.forall_mem_cons.2 ⟨subd2_6_0, List.forall_mem_cons.2 ⟨subd2_6_1, List.forall_mem_cons.2 ⟨subd2_6_2, List.forall_mem_cons.2 ⟨subd2_6_3, List.forall_mem_cons.2 ⟨subd2_6_4, List.forall_mem_cons.2 ⟨subd2_6_5, List.forall_mem_cons.2 ⟨subd2_6_6, List.forall_mem_cons.2 ⟨subd2_6_7, List.forall_mem_cons.2 ⟨subd2_6_8, List.forall_mem_cons.2 ⟨subd2_6_9, List.forall_mem_cons.2 ⟨subd2_6_10, List.forall_mem_cons.2 ⟨subd2_6_11, List.forall_mem_cons.2 ⟨subd2_6_12, List.forall_mem_cons.2 ⟨subd2_6_13, List.forall_mem_cons.2 ⟨subd2_6_14, List.forall_mem_cons.2 ⟨subd2_6_15, List.forall_mem_cons.2 ⟨subd2_6_16, List.forall_mem_cons.2 ⟨subd2_6_17, List.forall_mem_cons.2 ⟨subd2_6_18, List.forall_mem_cons.2 ⟨subd2_6_19, List.forall_mem_cons.2 ⟨subd2_6_20, List.forall_mem_cons.2 ⟨subd2_6_21, List.forall_mem_cons.2 ⟨subd2_6_22, List.forall_mem_cons.2 ⟨subd2_6_23, List.forall_mem_cons.2 ⟨subd2_6_24, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd2_7 : ldCheck G d2_7.U d2_7.ms ldd2_7 = true := by decide +kernel
theorem pre_okd2_7 : subPre G cell2 d2_7 = true := by decide +kernel
theorem subd2_7_0 : subd2_7 [-2] = true := by decide +kernel
theorem subd2_7_1 : subd2_7 [-1] = true := by decide +kernel
theorem subd2_7_2 : subd2_7 [0, -3] = true := by decide +kernel
theorem subd2_7_3 : subd2_7 [0, -2] = true := by decide +kernel
theorem subd2_7_4 : subd2_7 [0, -1] = true := by decide +kernel
theorem subd2_7_5 : subd2_7 [0, 0] = true := by decide +kernel
theorem subd2_7_6 : subd2_7 [0, 1] = true := by decide +kernel
theorem subd2_7_7 : subd2_7 [0, 2] = true := by decide +kernel
theorem subd2_7_8 : subd2_7 [1] = true := by decide +kernel
theorem subd2_7_9 : subd2_7 [2] = true := by decide +kernel
theorem sbd2_7_0 : ∀ q ∈ blkd2_7_0, subd2_7 q = true := by
  unfold blkd2_7_0
  exact List.forall_mem_cons.2 ⟨subd2_7_0, List.forall_mem_cons.2 ⟨subd2_7_1, List.forall_mem_cons.2 ⟨subd2_7_2, List.forall_mem_cons.2 ⟨subd2_7_3, List.forall_mem_cons.2 ⟨subd2_7_4, List.forall_mem_cons.2 ⟨subd2_7_5, List.forall_mem_cons.2 ⟨subd2_7_6, List.forall_mem_cons.2 ⟨subd2_7_7, List.forall_mem_cons.2 ⟨subd2_7_8, List.forall_mem_cons.2 ⟨subd2_7_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd3_0 : ldCheck G d3_0.U d3_0.ms ldd3_0 = true := by decide +kernel
theorem pre_okd3_0 : subPre G cell3 d3_0 = true := by decide +kernel
theorem subd3_0_0 : subd3_0 [-2] = true := by decide +kernel
theorem subd3_0_1 : subd3_0 [-1, -3] = true := by decide +kernel
theorem subd3_0_2 : subd3_0 [-1, -2] = true := by decide +kernel
theorem subd3_0_3 : subd3_0 [-1, -1] = true := by decide +kernel
theorem subd3_0_4 : subd3_0 [-1, 0] = true := by decide +kernel
theorem subd3_0_5 : subd3_0 [-1, 1] = true := by decide +kernel
theorem subd3_0_6 : subd3_0 [-1, 2] = true := by decide +kernel
theorem subd3_0_7 : subd3_0 [0, -3] = true := by decide +kernel
theorem subd3_0_8 : subd3_0 [0, -2] = true := by decide +kernel
theorem subd3_0_9 : subd3_0 [0, -1] = true := by decide +kernel
theorem subd3_0_10 : subd3_0 [0, 0] = true := by decide +kernel
theorem subd3_0_11 : subd3_0 [0, 1] = true := by decide +kernel
theorem subd3_0_12 : subd3_0 [0, 2] = true := by decide +kernel
theorem subd3_0_13 : subd3_0 [1, -3] = true := by decide +kernel
theorem subd3_0_14 : subd3_0 [1, -2] = true := by decide +kernel
theorem subd3_0_15 : subd3_0 [1, -1] = true := by decide +kernel
theorem subd3_0_16 : subd3_0 [1, 0] = true := by decide +kernel
theorem subd3_0_17 : subd3_0 [1, 1] = true := by decide +kernel
theorem subd3_0_18 : subd3_0 [1, 2] = true := by decide +kernel
theorem subd3_0_19 : subd3_0 [2] = true := by decide +kernel
theorem sbd3_0_0 : ∀ q ∈ blkd3_0_0, subd3_0 q = true := by
  unfold blkd3_0_0
  exact List.forall_mem_cons.2 ⟨subd3_0_0, List.forall_mem_cons.2 ⟨subd3_0_1, List.forall_mem_cons.2 ⟨subd3_0_2, List.forall_mem_cons.2 ⟨subd3_0_3, List.forall_mem_cons.2 ⟨subd3_0_4, List.forall_mem_cons.2 ⟨subd3_0_5, List.forall_mem_cons.2 ⟨subd3_0_6, List.forall_mem_cons.2 ⟨subd3_0_7, List.forall_mem_cons.2 ⟨subd3_0_8, List.forall_mem_cons.2 ⟨subd3_0_9, List.forall_mem_cons.2 ⟨subd3_0_10, List.forall_mem_cons.2 ⟨subd3_0_11, List.forall_mem_cons.2 ⟨subd3_0_12, List.forall_mem_cons.2 ⟨subd3_0_13, List.forall_mem_cons.2 ⟨subd3_0_14, List.forall_mem_cons.2 ⟨subd3_0_15, List.forall_mem_cons.2 ⟨subd3_0_16, List.forall_mem_cons.2 ⟨subd3_0_17, List.forall_mem_cons.2 ⟨subd3_0_18, List.forall_mem_cons.2 ⟨subd3_0_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd3_1 : ldCheck G d3_1.U d3_1.ms ldd3_1 = true := by decide +kernel
theorem pre_okd3_1 : subPre G cell3 d3_1 = true := by decide +kernel
theorem subd3_1_0 : subd3_1 [-6] = true := by decide +kernel
theorem subd3_1_1 : subd3_1 [-5, -6] = true := by decide +kernel
theorem subd3_1_2 : subd3_1 [-5, -5] = true := by decide +kernel
theorem subd3_1_3 : subd3_1 [-5, -4] = true := by decide +kernel
theorem subd3_1_4 : subd3_1 [-5, -3] = true := by decide +kernel
theorem subd3_1_5 : subd3_1 [-5, -2] = true := by decide +kernel
theorem subd3_1_6 : subd3_1 [-5, -1] = true := by decide +kernel
theorem subd3_1_7 : subd3_1 [-5, 0] = true := by decide +kernel
theorem subd3_1_8 : subd3_1 [-4, -7] = true := by decide +kernel
theorem subd3_1_9 : subd3_1 [-4, -6] = true := by decide +kernel
theorem subd3_1_10 : subd3_1 [-4, -5] = true := by decide +kernel
theorem subd3_1_11 : subd3_1 [-4, -4] = true := by decide +kernel
theorem subd3_1_12 : subd3_1 [-4, -3] = true := by decide +kernel
theorem subd3_1_13 : subd3_1 [-4, -2] = true := by decide +kernel
theorem subd3_1_14 : subd3_1 [-4, -1] = true := by decide +kernel
theorem subd3_1_15 : subd3_1 [-4, 0] = true := by decide +kernel
theorem subd3_1_16 : subd3_1 [-4, 1] = true := by decide +kernel
theorem subd3_1_17 : subd3_1 [-4, 2] = true := by decide +kernel
theorem subd3_1_18 : subd3_1 [-3, -7] = true := by decide +kernel
theorem subd3_1_19 : subd3_1 [-3, -6] = true := by decide +kernel
theorem subd3_1_20 : subd3_1 [-3, -5] = true := by decide +kernel
theorem subd3_1_21 : subd3_1 [-3, -4] = true := by decide +kernel
theorem subd3_1_22 : subd3_1 [-3, -3] = true := by decide +kernel
theorem subd3_1_23 : subd3_1 [-3, -2] = true := by decide +kernel
theorem subd3_1_24 : subd3_1 [-3, -1] = true := by decide +kernel
theorem subd3_1_25 : subd3_1 [-3, 0] = true := by decide +kernel
theorem subd3_1_26 : subd3_1 [-3, 1] = true := by decide +kernel
theorem subd3_1_27 : subd3_1 [-3, 2] = true := by decide +kernel
theorem subd3_1_28 : subd3_1 [-3, 3] = true := by decide +kernel
theorem subd3_1_29 : subd3_1 [-2, -7] = true := by decide +kernel
theorem subd3_1_30 : subd3_1 [-2, -6] = true := by decide +kernel
theorem subd3_1_31 : subd3_1 [-2, -5] = true := by decide +kernel
theorem sbd3_1_0 : ∀ q ∈ blkd3_1_0, subd3_1 q = true := by
  unfold blkd3_1_0
  exact List.forall_mem_cons.2 ⟨subd3_1_0, List.forall_mem_cons.2 ⟨subd3_1_1, List.forall_mem_cons.2 ⟨subd3_1_2, List.forall_mem_cons.2 ⟨subd3_1_3, List.forall_mem_cons.2 ⟨subd3_1_4, List.forall_mem_cons.2 ⟨subd3_1_5, List.forall_mem_cons.2 ⟨subd3_1_6, List.forall_mem_cons.2 ⟨subd3_1_7, List.forall_mem_cons.2 ⟨subd3_1_8, List.forall_mem_cons.2 ⟨subd3_1_9, List.forall_mem_cons.2 ⟨subd3_1_10, List.forall_mem_cons.2 ⟨subd3_1_11, List.forall_mem_cons.2 ⟨subd3_1_12, List.forall_mem_cons.2 ⟨subd3_1_13, List.forall_mem_cons.2 ⟨subd3_1_14, List.forall_mem_cons.2 ⟨subd3_1_15, List.forall_mem_cons.2 ⟨subd3_1_16, List.forall_mem_cons.2 ⟨subd3_1_17, List.forall_mem_cons.2 ⟨subd3_1_18, List.forall_mem_cons.2 ⟨subd3_1_19, List.forall_mem_cons.2 ⟨subd3_1_20, List.forall_mem_cons.2 ⟨subd3_1_21, List.forall_mem_cons.2 ⟨subd3_1_22, List.forall_mem_cons.2 ⟨subd3_1_23, List.forall_mem_cons.2 ⟨subd3_1_24, List.forall_mem_cons.2 ⟨subd3_1_25, List.forall_mem_cons.2 ⟨subd3_1_26, List.forall_mem_cons.2 ⟨subd3_1_27, List.forall_mem_cons.2 ⟨subd3_1_28, List.forall_mem_cons.2 ⟨subd3_1_29, List.forall_mem_cons.2 ⟨subd3_1_30, List.forall_mem_cons.2 ⟨subd3_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C128
