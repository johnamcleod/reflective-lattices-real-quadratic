import ReflectZphi.Data.Cert5.C134.Base

namespace ReflectZphi.Data.Cert5.C134

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd2_7_0 : subd2_7 [-2, -2] = true := by decide +kernel
theorem subd2_7_1 : subd2_7 [-2, -1] = true := by decide +kernel
theorem subd2_7_2 : subd2_7 [-2, 0] = true := by decide +kernel
theorem subd2_7_3 : subd2_7 [-2, 1] = true := by decide +kernel
theorem subd2_7_4 : subd2_7 [-2, 2] = true := by decide +kernel
theorem subd2_7_5 : subd2_7 [-1, -3] = true := by decide +kernel
theorem subd2_7_6 : subd2_7 [-1, -2] = true := by decide +kernel
theorem subd2_7_7 : subd2_7 [-1, -1] = true := by decide +kernel
theorem subd2_7_8 : subd2_7 [-1, 0] = true := by decide +kernel
theorem subd2_7_9 : subd2_7 [-1, 1] = true := by decide +kernel
theorem subd2_7_10 : subd2_7 [-1, 2] = true := by decide +kernel
theorem subd2_7_11 : subd2_7 [-1, 3] = true := by decide +kernel
theorem subd2_7_12 : subd2_7 [0, -4] = true := by decide +kernel
theorem subd2_7_13 : subd2_7 [0, -3] = true := by decide +kernel
theorem subd2_7_14 : subd2_7 [0, -2] = true := by decide +kernel
theorem subd2_7_15 : subd2_7 [0, -1] = true := by decide +kernel
theorem subd2_7_16 : subd2_7 [0, 0] = true := by decide +kernel
theorem subd2_7_17 : subd2_7 [0, 1] = true := by decide +kernel
theorem subd2_7_18 : subd2_7 [0, 2] = true := by decide +kernel
theorem subd2_7_19 : subd2_7 [0, 3] = true := by decide +kernel
theorem subd2_7_20 : subd2_7 [1, -4] = true := by decide +kernel
theorem subd2_7_21 : subd2_7 [1, -3] = true := by decide +kernel
theorem subd2_7_22 : subd2_7 [1, -2] = true := by decide +kernel
theorem subd2_7_23 : subd2_7 [1, -1] = true := by decide +kernel
theorem subd2_7_24 : subd2_7 [1, 0] = true := by decide +kernel
theorem subd2_7_25 : subd2_7 [1, 1] = true := by decide +kernel
theorem subd2_7_26 : subd2_7 [1, 2] = true := by decide +kernel
theorem subd2_7_27 : subd2_7 [2, -3] = true := by decide +kernel
theorem subd2_7_28 : subd2_7 [2, -2] = true := by decide +kernel
theorem subd2_7_29 : subd2_7 [2, -1] = true := by decide +kernel
theorem subd2_7_30 : subd2_7 [2, 0] = true := by decide +kernel
theorem subd2_7_31 : subd2_7 [2, 1] = true := by decide +kernel
theorem sbd2_7_0 : ∀ q ∈ blkd2_7_0, subd2_7 q = true := by
  unfold blkd2_7_0
  exact List.forall_mem_cons.2 ⟨subd2_7_0, List.forall_mem_cons.2 ⟨subd2_7_1, List.forall_mem_cons.2 ⟨subd2_7_2, List.forall_mem_cons.2 ⟨subd2_7_3, List.forall_mem_cons.2 ⟨subd2_7_4, List.forall_mem_cons.2 ⟨subd2_7_5, List.forall_mem_cons.2 ⟨subd2_7_6, List.forall_mem_cons.2 ⟨subd2_7_7, List.forall_mem_cons.2 ⟨subd2_7_8, List.forall_mem_cons.2 ⟨subd2_7_9, List.forall_mem_cons.2 ⟨subd2_7_10, List.forall_mem_cons.2 ⟨subd2_7_11, List.forall_mem_cons.2 ⟨subd2_7_12, List.forall_mem_cons.2 ⟨subd2_7_13, List.forall_mem_cons.2 ⟨subd2_7_14, List.forall_mem_cons.2 ⟨subd2_7_15, List.forall_mem_cons.2 ⟨subd2_7_16, List.forall_mem_cons.2 ⟨subd2_7_17, List.forall_mem_cons.2 ⟨subd2_7_18, List.forall_mem_cons.2 ⟨subd2_7_19, List.forall_mem_cons.2 ⟨subd2_7_20, List.forall_mem_cons.2 ⟨subd2_7_21, List.forall_mem_cons.2 ⟨subd2_7_22, List.forall_mem_cons.2 ⟨subd2_7_23, List.forall_mem_cons.2 ⟨subd2_7_24, List.forall_mem_cons.2 ⟨subd2_7_25, List.forall_mem_cons.2 ⟨subd2_7_26, List.forall_mem_cons.2 ⟨subd2_7_27, List.forall_mem_cons.2 ⟨subd2_7_28, List.forall_mem_cons.2 ⟨subd2_7_29, List.forall_mem_cons.2 ⟨subd2_7_30, List.forall_mem_cons.2 ⟨subd2_7_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd3_0 : ldCheck G d3_0.U d3_0.ms ldd3_0 = true := by decide +kernel
theorem pre_okd3_0 : subPre G cell3 d3_0 = true := by decide +kernel
theorem subd3_0_0 : subd3_0 [-3] = true := by decide +kernel
theorem subd3_0_1 : subd3_0 [-2, -4] = true := by decide +kernel
theorem subd3_0_2 : subd3_0 [-2, -3] = true := by decide +kernel
theorem subd3_0_3 : subd3_0 [-2, -2] = true := by decide +kernel
theorem subd3_0_4 : subd3_0 [-2, -1] = true := by decide +kernel
theorem subd3_0_5 : subd3_0 [-2, 0] = true := by decide +kernel
theorem subd3_0_6 : subd3_0 [-2, 1] = true := by decide +kernel
theorem subd3_0_7 : subd3_0 [-2, 2] = true := by decide +kernel
theorem subd3_0_8 : subd3_0 [-2, 3] = true := by decide +kernel
theorem subd3_0_9 : subd3_0 [-1, -4] = true := by decide +kernel
theorem subd3_0_10 : subd3_0 [-1, -3] = true := by decide +kernel
theorem subd3_0_11 : subd3_0 [-1, -2] = true := by decide +kernel
theorem subd3_0_12 : subd3_0 [-1, -1] = true := by decide +kernel
theorem subd3_0_13 : subd3_0 [-1, 0] = true := by decide +kernel
theorem subd3_0_14 : subd3_0 [-1, 1] = true := by decide +kernel
theorem subd3_0_15 : subd3_0 [-1, 2] = true := by decide +kernel
theorem subd3_0_16 : subd3_0 [-1, 3] = true := by decide +kernel
theorem subd3_0_17 : subd3_0 [0, -5] = true := by decide +kernel
theorem subd3_0_18 : subd3_0 [0, -4] = true := by decide +kernel
theorem subd3_0_19 : subd3_0 [0, -3] = true := by decide +kernel
theorem subd3_0_20 : subd3_0 [0, -2] = true := by decide +kernel
theorem subd3_0_21 : subd3_0 [0, -1] = true := by decide +kernel
theorem subd3_0_22 : subd3_0 [0, 0] = true := by decide +kernel
theorem subd3_0_23 : subd3_0 [0, 1] = true := by decide +kernel
theorem subd3_0_24 : subd3_0 [0, 2] = true := by decide +kernel
theorem subd3_0_25 : subd3_0 [0, 3] = true := by decide +kernel
theorem subd3_0_26 : subd3_0 [0, 4] = true := by decide +kernel
theorem subd3_0_27 : subd3_0 [1, -4] = true := by decide +kernel
theorem subd3_0_28 : subd3_0 [1, -3] = true := by decide +kernel
theorem subd3_0_29 : subd3_0 [1, -2] = true := by decide +kernel
theorem subd3_0_30 : subd3_0 [1, -1] = true := by decide +kernel
theorem subd3_0_31 : subd3_0 [1, 0] = true := by decide +kernel
theorem sbd3_0_0 : ∀ q ∈ blkd3_0_0, subd3_0 q = true := by
  unfold blkd3_0_0
  exact List.forall_mem_cons.2 ⟨subd3_0_0, List.forall_mem_cons.2 ⟨subd3_0_1, List.forall_mem_cons.2 ⟨subd3_0_2, List.forall_mem_cons.2 ⟨subd3_0_3, List.forall_mem_cons.2 ⟨subd3_0_4, List.forall_mem_cons.2 ⟨subd3_0_5, List.forall_mem_cons.2 ⟨subd3_0_6, List.forall_mem_cons.2 ⟨subd3_0_7, List.forall_mem_cons.2 ⟨subd3_0_8, List.forall_mem_cons.2 ⟨subd3_0_9, List.forall_mem_cons.2 ⟨subd3_0_10, List.forall_mem_cons.2 ⟨subd3_0_11, List.forall_mem_cons.2 ⟨subd3_0_12, List.forall_mem_cons.2 ⟨subd3_0_13, List.forall_mem_cons.2 ⟨subd3_0_14, List.forall_mem_cons.2 ⟨subd3_0_15, List.forall_mem_cons.2 ⟨subd3_0_16, List.forall_mem_cons.2 ⟨subd3_0_17, List.forall_mem_cons.2 ⟨subd3_0_18, List.forall_mem_cons.2 ⟨subd3_0_19, List.forall_mem_cons.2 ⟨subd3_0_20, List.forall_mem_cons.2 ⟨subd3_0_21, List.forall_mem_cons.2 ⟨subd3_0_22, List.forall_mem_cons.2 ⟨subd3_0_23, List.forall_mem_cons.2 ⟨subd3_0_24, List.forall_mem_cons.2 ⟨subd3_0_25, List.forall_mem_cons.2 ⟨subd3_0_26, List.forall_mem_cons.2 ⟨subd3_0_27, List.forall_mem_cons.2 ⟨subd3_0_28, List.forall_mem_cons.2 ⟨subd3_0_29, List.forall_mem_cons.2 ⟨subd3_0_30, List.forall_mem_cons.2 ⟨subd3_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_0_32 : subd3_0 [1, 1] = true := by decide +kernel
theorem subd3_0_33 : subd3_0 [1, 2] = true := by decide +kernel
theorem subd3_0_34 : subd3_0 [1, 3] = true := by decide +kernel
theorem subd3_0_35 : subd3_0 [2, -4] = true := by decide +kernel
theorem subd3_0_36 : subd3_0 [2, -3] = true := by decide +kernel
theorem subd3_0_37 : subd3_0 [2, -2] = true := by decide +kernel
theorem subd3_0_38 : subd3_0 [2, -1] = true := by decide +kernel
theorem subd3_0_39 : subd3_0 [2, 0] = true := by decide +kernel
theorem subd3_0_40 : subd3_0 [2, 1] = true := by decide +kernel
theorem subd3_0_41 : subd3_0 [2, 2] = true := by decide +kernel
theorem subd3_0_42 : subd3_0 [2, 3] = true := by decide +kernel
theorem subd3_0_43 : subd3_0 [3] = true := by decide +kernel
theorem sbd3_0_1 : ∀ q ∈ blkd3_0_1, subd3_0 q = true := by
  unfold blkd3_0_1
  exact List.forall_mem_cons.2 ⟨subd3_0_32, List.forall_mem_cons.2 ⟨subd3_0_33, List.forall_mem_cons.2 ⟨subd3_0_34, List.forall_mem_cons.2 ⟨subd3_0_35, List.forall_mem_cons.2 ⟨subd3_0_36, List.forall_mem_cons.2 ⟨subd3_0_37, List.forall_mem_cons.2 ⟨subd3_0_38, List.forall_mem_cons.2 ⟨subd3_0_39, List.forall_mem_cons.2 ⟨subd3_0_40, List.forall_mem_cons.2 ⟨subd3_0_41, List.forall_mem_cons.2 ⟨subd3_0_42, List.forall_mem_cons.2 ⟨subd3_0_43, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd3_1 : ldCheck G d3_1.U d3_1.ms ldd3_1 = true := by decide +kernel
theorem pre_okd3_1 : subPre G cell3 d3_1 = true := by decide +kernel
theorem subd3_1_0 : subd3_1 [-2] = true := by decide +kernel
theorem subd3_1_1 : subd3_1 [-1, -3] = true := by decide +kernel
theorem subd3_1_2 : subd3_1 [-1, -2] = true := by decide +kernel
theorem subd3_1_3 : subd3_1 [-1, -1] = true := by decide +kernel
theorem subd3_1_4 : subd3_1 [-1, 0] = true := by decide +kernel
theorem subd3_1_5 : subd3_1 [-1, 1] = true := by decide +kernel
theorem subd3_1_6 : subd3_1 [-1, 2] = true := by decide +kernel
theorem subd3_1_7 : subd3_1 [0, -3] = true := by decide +kernel
theorem subd3_1_8 : subd3_1 [0, -2] = true := by decide +kernel
theorem subd3_1_9 : subd3_1 [0, -1] = true := by decide +kernel
theorem subd3_1_10 : subd3_1 [0, 0] = true := by decide +kernel
theorem subd3_1_11 : subd3_1 [0, 1] = true := by decide +kernel
theorem subd3_1_12 : subd3_1 [0, 2] = true := by decide +kernel
theorem subd3_1_13 : subd3_1 [1, -3] = true := by decide +kernel
theorem subd3_1_14 : subd3_1 [1, -2] = true := by decide +kernel
theorem subd3_1_15 : subd3_1 [1, -1] = true := by decide +kernel
theorem subd3_1_16 : subd3_1 [1, 0] = true := by decide +kernel
theorem subd3_1_17 : subd3_1 [1, 1] = true := by decide +kernel
theorem subd3_1_18 : subd3_1 [1, 2] = true := by decide +kernel
theorem subd3_1_19 : subd3_1 [2] = true := by decide +kernel
theorem sbd3_1_0 : ∀ q ∈ blkd3_1_0, subd3_1 q = true := by
  unfold blkd3_1_0
  exact List.forall_mem_cons.2 ⟨subd3_1_0, List.forall_mem_cons.2 ⟨subd3_1_1, List.forall_mem_cons.2 ⟨subd3_1_2, List.forall_mem_cons.2 ⟨subd3_1_3, List.forall_mem_cons.2 ⟨subd3_1_4, List.forall_mem_cons.2 ⟨subd3_1_5, List.forall_mem_cons.2 ⟨subd3_1_6, List.forall_mem_cons.2 ⟨subd3_1_7, List.forall_mem_cons.2 ⟨subd3_1_8, List.forall_mem_cons.2 ⟨subd3_1_9, List.forall_mem_cons.2 ⟨subd3_1_10, List.forall_mem_cons.2 ⟨subd3_1_11, List.forall_mem_cons.2 ⟨subd3_1_12, List.forall_mem_cons.2 ⟨subd3_1_13, List.forall_mem_cons.2 ⟨subd3_1_14, List.forall_mem_cons.2 ⟨subd3_1_15, List.forall_mem_cons.2 ⟨subd3_1_16, List.forall_mem_cons.2 ⟨subd3_1_17, List.forall_mem_cons.2 ⟨subd3_1_18, List.forall_mem_cons.2 ⟨subd3_1_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd3_2 : ldCheck G d3_2.U d3_2.ms ldd3_2 = true := by decide +kernel
theorem pre_okd3_2 : subPre G cell3 d3_2 = true := by decide +kernel
theorem subd3_2_0 : subd3_2 [-2] = true := by decide +kernel
theorem subd3_2_1 : subd3_2 [-1, -3] = true := by decide +kernel
theorem subd3_2_2 : subd3_2 [-1, -2] = true := by decide +kernel
theorem subd3_2_3 : subd3_2 [-1, -1] = true := by decide +kernel
theorem subd3_2_4 : subd3_2 [-1, 0] = true := by decide +kernel
theorem subd3_2_5 : subd3_2 [-1, 1] = true := by decide +kernel
theorem subd3_2_6 : subd3_2 [-1, 2] = true := by decide +kernel
theorem subd3_2_7 : subd3_2 [0, -3] = true := by decide +kernel
theorem subd3_2_8 : subd3_2 [0, -2] = true := by decide +kernel
theorem subd3_2_9 : subd3_2 [0, -1] = true := by decide +kernel
theorem subd3_2_10 : subd3_2 [0, 0] = true := by decide +kernel
theorem subd3_2_11 : subd3_2 [0, 1] = true := by decide +kernel
theorem subd3_2_12 : subd3_2 [0, 2] = true := by decide +kernel
theorem subd3_2_13 : subd3_2 [1, -3] = true := by decide +kernel
theorem subd3_2_14 : subd3_2 [1, -2] = true := by decide +kernel
theorem subd3_2_15 : subd3_2 [1, -1] = true := by decide +kernel
theorem subd3_2_16 : subd3_2 [1, 0] = true := by decide +kernel
theorem subd3_2_17 : subd3_2 [1, 1] = true := by decide +kernel
theorem subd3_2_18 : subd3_2 [1, 2] = true := by decide +kernel
theorem subd3_2_19 : subd3_2 [2] = true := by decide +kernel
theorem sbd3_2_0 : ∀ q ∈ blkd3_2_0, subd3_2 q = true := by
  unfold blkd3_2_0
  exact List.forall_mem_cons.2 ⟨subd3_2_0, List.forall_mem_cons.2 ⟨subd3_2_1, List.forall_mem_cons.2 ⟨subd3_2_2, List.forall_mem_cons.2 ⟨subd3_2_3, List.forall_mem_cons.2 ⟨subd3_2_4, List.forall_mem_cons.2 ⟨subd3_2_5, List.forall_mem_cons.2 ⟨subd3_2_6, List.forall_mem_cons.2 ⟨subd3_2_7, List.forall_mem_cons.2 ⟨subd3_2_8, List.forall_mem_cons.2 ⟨subd3_2_9, List.forall_mem_cons.2 ⟨subd3_2_10, List.forall_mem_cons.2 ⟨subd3_2_11, List.forall_mem_cons.2 ⟨subd3_2_12, List.forall_mem_cons.2 ⟨subd3_2_13, List.forall_mem_cons.2 ⟨subd3_2_14, List.forall_mem_cons.2 ⟨subd3_2_15, List.forall_mem_cons.2 ⟨subd3_2_16, List.forall_mem_cons.2 ⟨subd3_2_17, List.forall_mem_cons.2 ⟨subd3_2_18, List.forall_mem_cons.2 ⟨subd3_2_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C134
