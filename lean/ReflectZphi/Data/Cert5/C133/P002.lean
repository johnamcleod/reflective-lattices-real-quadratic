import ReflectZphi.Data.Cert5.C133.Base

namespace ReflectZphi.Data.Cert5.C133

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd2_3_0 : subd2_3 [-3] = true := by decide +kernel
theorem subd2_3_1 : subd2_3 [-2, -3] = true := by decide +kernel
theorem subd2_3_2 : subd2_3 [-2, -2] = true := by decide +kernel
theorem subd2_3_3 : subd2_3 [-2, -1] = true := by decide +kernel
theorem subd2_3_4 : subd2_3 [-2, 0] = true := by decide +kernel
theorem subd2_3_5 : subd2_3 [-2, 1] = true := by decide +kernel
theorem subd2_3_6 : subd2_3 [-2, 2] = true := by decide +kernel
theorem subd2_3_7 : subd2_3 [-1, -4] = true := by decide +kernel
theorem subd2_3_8 : subd2_3 [-1, -3] = true := by decide +kernel
theorem subd2_3_9 : subd2_3 [-1, -2] = true := by decide +kernel
theorem subd2_3_10 : subd2_3 [-1, -1] = true := by decide +kernel
theorem subd2_3_11 : subd2_3 [-1, 0] = true := by decide +kernel
theorem subd2_3_12 : subd2_3 [-1, 1] = true := by decide +kernel
theorem subd2_3_13 : subd2_3 [-1, 2] = true := by decide +kernel
theorem subd2_3_14 : subd2_3 [-1, 3] = true := by decide +kernel
theorem subd2_3_15 : subd2_3 [0, -4] = true := by decide +kernel
theorem subd2_3_16 : subd2_3 [0, -3] = true := by decide +kernel
theorem subd2_3_17 : subd2_3 [0, -2] = true := by decide +kernel
theorem subd2_3_18 : subd2_3 [0, -1] = true := by decide +kernel
theorem subd2_3_19 : subd2_3 [0, 0] = true := by decide +kernel
theorem subd2_3_20 : subd2_3 [0, 1] = true := by decide +kernel
theorem subd2_3_21 : subd2_3 [0, 2] = true := by decide +kernel
theorem subd2_3_22 : subd2_3 [0, 3] = true := by decide +kernel
theorem subd2_3_23 : subd2_3 [1, -4] = true := by decide +kernel
theorem subd2_3_24 : subd2_3 [1, -3] = true := by decide +kernel
theorem subd2_3_25 : subd2_3 [1, -2] = true := by decide +kernel
theorem subd2_3_26 : subd2_3 [1, -1] = true := by decide +kernel
theorem subd2_3_27 : subd2_3 [1, 0] = true := by decide +kernel
theorem subd2_3_28 : subd2_3 [1, 1] = true := by decide +kernel
theorem subd2_3_29 : subd2_3 [1, 2] = true := by decide +kernel
theorem subd2_3_30 : subd2_3 [1, 3] = true := by decide +kernel
theorem subd2_3_31 : subd2_3 [2, -3] = true := by decide +kernel
theorem sbd2_3_0 : ∀ q ∈ blkd2_3_0, subd2_3 q = true := by
  unfold blkd2_3_0
  exact List.forall_mem_cons.2 ⟨subd2_3_0, List.forall_mem_cons.2 ⟨subd2_3_1, List.forall_mem_cons.2 ⟨subd2_3_2, List.forall_mem_cons.2 ⟨subd2_3_3, List.forall_mem_cons.2 ⟨subd2_3_4, List.forall_mem_cons.2 ⟨subd2_3_5, List.forall_mem_cons.2 ⟨subd2_3_6, List.forall_mem_cons.2 ⟨subd2_3_7, List.forall_mem_cons.2 ⟨subd2_3_8, List.forall_mem_cons.2 ⟨subd2_3_9, List.forall_mem_cons.2 ⟨subd2_3_10, List.forall_mem_cons.2 ⟨subd2_3_11, List.forall_mem_cons.2 ⟨subd2_3_12, List.forall_mem_cons.2 ⟨subd2_3_13, List.forall_mem_cons.2 ⟨subd2_3_14, List.forall_mem_cons.2 ⟨subd2_3_15, List.forall_mem_cons.2 ⟨subd2_3_16, List.forall_mem_cons.2 ⟨subd2_3_17, List.forall_mem_cons.2 ⟨subd2_3_18, List.forall_mem_cons.2 ⟨subd2_3_19, List.forall_mem_cons.2 ⟨subd2_3_20, List.forall_mem_cons.2 ⟨subd2_3_21, List.forall_mem_cons.2 ⟨subd2_3_22, List.forall_mem_cons.2 ⟨subd2_3_23, List.forall_mem_cons.2 ⟨subd2_3_24, List.forall_mem_cons.2 ⟨subd2_3_25, List.forall_mem_cons.2 ⟨subd2_3_26, List.forall_mem_cons.2 ⟨subd2_3_27, List.forall_mem_cons.2 ⟨subd2_3_28, List.forall_mem_cons.2 ⟨subd2_3_29, List.forall_mem_cons.2 ⟨subd2_3_30, List.forall_mem_cons.2 ⟨subd2_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd2_3_32 : subd2_3 [2, -2] = true := by decide +kernel
theorem subd2_3_33 : subd2_3 [2, -1] = true := by decide +kernel
theorem subd2_3_34 : subd2_3 [2, 0] = true := by decide +kernel
theorem subd2_3_35 : subd2_3 [2, 1] = true := by decide +kernel
theorem subd2_3_36 : subd2_3 [2, 2] = true := by decide +kernel
theorem subd2_3_37 : subd2_3 [3] = true := by decide +kernel
theorem sbd2_3_1 : ∀ q ∈ blkd2_3_1, subd2_3 q = true := by
  unfold blkd2_3_1
  exact List.forall_mem_cons.2 ⟨subd2_3_32, List.forall_mem_cons.2 ⟨subd2_3_33, List.forall_mem_cons.2 ⟨subd2_3_34, List.forall_mem_cons.2 ⟨subd2_3_35, List.forall_mem_cons.2 ⟨subd2_3_36, List.forall_mem_cons.2 ⟨subd2_3_37, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem ld_okd3_0 : ldCheck G d3_0.U d3_0.ms ldd3_0 = true := by decide +kernel
theorem pre_okd3_0 : subPre G cell3 d3_0 = true := by decide +kernel
theorem subd3_0_0 : subd3_0 [-1] = true := by decide +kernel
theorem subd3_0_1 : subd3_0 [0] = true := by decide +kernel
theorem subd3_0_2 : subd3_0 [1] = true := by decide +kernel
theorem sbd3_0_0 : ∀ q ∈ blkd3_0_0, subd3_0 q = true := by
  unfold blkd3_0_0
  exact List.forall_mem_cons.2 ⟨subd3_0_0, List.forall_mem_cons.2 ⟨subd3_0_1, List.forall_mem_cons.2 ⟨subd3_0_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd3_1 : ldCheck G d3_1.U d3_1.ms ldd3_1 = true := by decide +kernel
theorem pre_okd3_1 : subPre G cell3 d3_1 = true := by decide +kernel
theorem subd3_1_0 : subd3_1 [-2] = true := by decide +kernel
theorem subd3_1_1 : subd3_1 [-1] = true := by decide +kernel
theorem subd3_1_2 : subd3_1 [0] = true := by decide +kernel
theorem subd3_1_3 : subd3_1 [1] = true := by decide +kernel
theorem subd3_1_4 : subd3_1 [2] = true := by decide +kernel
theorem sbd3_1_0 : ∀ q ∈ blkd3_1_0, subd3_1 q = true := by
  unfold blkd3_1_0
  exact List.forall_mem_cons.2 ⟨subd3_1_0, List.forall_mem_cons.2 ⟨subd3_1_1, List.forall_mem_cons.2 ⟨subd3_1_2, List.forall_mem_cons.2 ⟨subd3_1_3, List.forall_mem_cons.2 ⟨subd3_1_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd3_2 : ldCheck G d3_2.U d3_2.ms ldd3_2 = true := by decide +kernel
theorem pre_okd3_2 : subPre G cell3 d3_2 = true := by decide +kernel
theorem subd3_2_0 : subd3_2 [-4] = true := by decide +kernel
theorem subd3_2_1 : subd3_2 [-3, -3] = true := by decide +kernel
theorem subd3_2_2 : subd3_2 [-3, -2] = true := by decide +kernel
theorem subd3_2_3 : subd3_2 [-3, -1] = true := by decide +kernel
theorem subd3_2_4 : subd3_2 [-3, 0] = true := by decide +kernel
theorem subd3_2_5 : subd3_2 [-3, 1] = true := by decide +kernel
theorem subd3_2_6 : subd3_2 [-3, 2] = true := by decide +kernel
theorem subd3_2_7 : subd3_2 [-3, 3] = true := by decide +kernel
theorem subd3_2_8 : subd3_2 [-3, 4] = true := by decide +kernel
theorem subd3_2_9 : subd3_2 [-3, 5] = true := by decide +kernel
theorem subd3_2_10 : subd3_2 [-2, -5] = true := by decide +kernel
theorem subd3_2_11 : subd3_2 [-2, -4] = true := by decide +kernel
theorem subd3_2_12 : subd3_2 [-2, -3] = true := by decide +kernel
theorem subd3_2_13 : subd3_2 [-2, -2] = true := by decide +kernel
theorem subd3_2_14 : subd3_2 [-2, -1] = true := by decide +kernel
theorem subd3_2_15 : subd3_2 [-2, 0] = true := by decide +kernel
theorem subd3_2_16 : subd3_2 [-2, 1] = true := by decide +kernel
theorem subd3_2_17 : subd3_2 [-2, 2] = true := by decide +kernel
theorem subd3_2_18 : subd3_2 [-2, 3] = true := by decide +kernel
theorem subd3_2_19 : subd3_2 [-2, 4] = true := by decide +kernel
theorem subd3_2_20 : subd3_2 [-2, 5] = true := by decide +kernel
theorem subd3_2_21 : subd3_2 [-1, -5] = true := by decide +kernel
theorem subd3_2_22 : subd3_2 [-1, -4] = true := by decide +kernel
theorem subd3_2_23 : subd3_2 [-1, -3] = true := by decide +kernel
theorem subd3_2_24 : subd3_2 [-1, -2] = true := by decide +kernel
theorem subd3_2_25 : subd3_2 [-1, -1] = true := by decide +kernel
theorem subd3_2_26 : subd3_2 [-1, 0] = true := by decide +kernel
theorem subd3_2_27 : subd3_2 [-1, 1] = true := by decide +kernel
theorem subd3_2_28 : subd3_2 [-1, 2] = true := by decide +kernel
theorem subd3_2_29 : subd3_2 [-1, 3] = true := by decide +kernel
theorem subd3_2_30 : subd3_2 [-1, 4] = true := by decide +kernel
theorem subd3_2_31 : subd3_2 [-1, 5] = true := by decide +kernel
theorem sbd3_2_0 : ∀ q ∈ blkd3_2_0, subd3_2 q = true := by
  unfold blkd3_2_0
  exact List.forall_mem_cons.2 ⟨subd3_2_0, List.forall_mem_cons.2 ⟨subd3_2_1, List.forall_mem_cons.2 ⟨subd3_2_2, List.forall_mem_cons.2 ⟨subd3_2_3, List.forall_mem_cons.2 ⟨subd3_2_4, List.forall_mem_cons.2 ⟨subd3_2_5, List.forall_mem_cons.2 ⟨subd3_2_6, List.forall_mem_cons.2 ⟨subd3_2_7, List.forall_mem_cons.2 ⟨subd3_2_8, List.forall_mem_cons.2 ⟨subd3_2_9, List.forall_mem_cons.2 ⟨subd3_2_10, List.forall_mem_cons.2 ⟨subd3_2_11, List.forall_mem_cons.2 ⟨subd3_2_12, List.forall_mem_cons.2 ⟨subd3_2_13, List.forall_mem_cons.2 ⟨subd3_2_14, List.forall_mem_cons.2 ⟨subd3_2_15, List.forall_mem_cons.2 ⟨subd3_2_16, List.forall_mem_cons.2 ⟨subd3_2_17, List.forall_mem_cons.2 ⟨subd3_2_18, List.forall_mem_cons.2 ⟨subd3_2_19, List.forall_mem_cons.2 ⟨subd3_2_20, List.forall_mem_cons.2 ⟨subd3_2_21, List.forall_mem_cons.2 ⟨subd3_2_22, List.forall_mem_cons.2 ⟨subd3_2_23, List.forall_mem_cons.2 ⟨subd3_2_24, List.forall_mem_cons.2 ⟨subd3_2_25, List.forall_mem_cons.2 ⟨subd3_2_26, List.forall_mem_cons.2 ⟨subd3_2_27, List.forall_mem_cons.2 ⟨subd3_2_28, List.forall_mem_cons.2 ⟨subd3_2_29, List.forall_mem_cons.2 ⟨subd3_2_30, List.forall_mem_cons.2 ⟨subd3_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C133
