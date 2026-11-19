import ReflectZphi.Data.Cert5.C140.Base

namespace ReflectZphi.Data.Cert5.C140

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_3_0 : subd6_3 [-3] = true := by decide +kernel
theorem subd6_3_1 : subd6_3 [-2, -4] = true := by decide +kernel
theorem subd6_3_2 : subd6_3 [-2, -3] = true := by decide +kernel
theorem subd6_3_3 : subd6_3 [-2, -2] = true := by decide +kernel
theorem subd6_3_4 : subd6_3 [-2, -1] = true := by decide +kernel
theorem subd6_3_5 : subd6_3 [-2, 0] = true := by decide +kernel
theorem subd6_3_6 : subd6_3 [-2, 1] = true := by decide +kernel
theorem subd6_3_7 : subd6_3 [-2, 2] = true := by decide +kernel
theorem subd6_3_8 : subd6_3 [-1, -4] = true := by decide +kernel
theorem subd6_3_9 : subd6_3 [-1, -3] = true := by decide +kernel
theorem subd6_3_10 : subd6_3 [-1, -2] = true := by decide +kernel
theorem subd6_3_11 : subd6_3 [-1, -1] = true := by decide +kernel
theorem subd6_3_12 : subd6_3 [-1, 0] = true := by decide +kernel
theorem subd6_3_13 : subd6_3 [-1, 1] = true := by decide +kernel
theorem subd6_3_14 : subd6_3 [-1, 2] = true := by decide +kernel
theorem subd6_3_15 : subd6_3 [-1, 3] = true := by decide +kernel
theorem subd6_3_16 : subd6_3 [0, -4] = true := by decide +kernel
theorem subd6_3_17 : subd6_3 [0, -3] = true := by decide +kernel
theorem subd6_3_18 : subd6_3 [0, -2] = true := by decide +kernel
theorem subd6_3_19 : subd6_3 [0, -1] = true := by decide +kernel
theorem subd6_3_20 : subd6_3 [0, 0] = true := by decide +kernel
theorem subd6_3_21 : subd6_3 [0, 1] = true := by decide +kernel
theorem subd6_3_22 : subd6_3 [0, 2] = true := by decide +kernel
theorem subd6_3_23 : subd6_3 [0, 3] = true := by decide +kernel
theorem subd6_3_24 : subd6_3 [1, -4] = true := by decide +kernel
theorem subd6_3_25 : subd6_3 [1, -3] = true := by decide +kernel
theorem subd6_3_26 : subd6_3 [1, -2] = true := by decide +kernel
theorem subd6_3_27 : subd6_3 [1, -1] = true := by decide +kernel
theorem subd6_3_28 : subd6_3 [1, 0] = true := by decide +kernel
theorem subd6_3_29 : subd6_3 [1, 1] = true := by decide +kernel
theorem subd6_3_30 : subd6_3 [1, 2] = true := by decide +kernel
theorem subd6_3_31 : subd6_3 [1, 3] = true := by decide +kernel
theorem sbd6_3_0 : ∀ q ∈ blkd6_3_0, subd6_3 q = true := by
  unfold blkd6_3_0
  exact List.forall_mem_cons.2 ⟨subd6_3_0, List.forall_mem_cons.2 ⟨subd6_3_1, List.forall_mem_cons.2 ⟨subd6_3_2, List.forall_mem_cons.2 ⟨subd6_3_3, List.forall_mem_cons.2 ⟨subd6_3_4, List.forall_mem_cons.2 ⟨subd6_3_5, List.forall_mem_cons.2 ⟨subd6_3_6, List.forall_mem_cons.2 ⟨subd6_3_7, List.forall_mem_cons.2 ⟨subd6_3_8, List.forall_mem_cons.2 ⟨subd6_3_9, List.forall_mem_cons.2 ⟨subd6_3_10, List.forall_mem_cons.2 ⟨subd6_3_11, List.forall_mem_cons.2 ⟨subd6_3_12, List.forall_mem_cons.2 ⟨subd6_3_13, List.forall_mem_cons.2 ⟨subd6_3_14, List.forall_mem_cons.2 ⟨subd6_3_15, List.forall_mem_cons.2 ⟨subd6_3_16, List.forall_mem_cons.2 ⟨subd6_3_17, List.forall_mem_cons.2 ⟨subd6_3_18, List.forall_mem_cons.2 ⟨subd6_3_19, List.forall_mem_cons.2 ⟨subd6_3_20, List.forall_mem_cons.2 ⟨subd6_3_21, List.forall_mem_cons.2 ⟨subd6_3_22, List.forall_mem_cons.2 ⟨subd6_3_23, List.forall_mem_cons.2 ⟨subd6_3_24, List.forall_mem_cons.2 ⟨subd6_3_25, List.forall_mem_cons.2 ⟨subd6_3_26, List.forall_mem_cons.2 ⟨subd6_3_27, List.forall_mem_cons.2 ⟨subd6_3_28, List.forall_mem_cons.2 ⟨subd6_3_29, List.forall_mem_cons.2 ⟨subd6_3_30, List.forall_mem_cons.2 ⟨subd6_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_3_32 : subd6_3 [2, -3] = true := by decide +kernel
theorem subd6_3_33 : subd6_3 [2, -2] = true := by decide +kernel
theorem subd6_3_34 : subd6_3 [2, -1] = true := by decide +kernel
theorem subd6_3_35 : subd6_3 [2, 0] = true := by decide +kernel
theorem subd6_3_36 : subd6_3 [2, 1] = true := by decide +kernel
theorem subd6_3_37 : subd6_3 [2, 2] = true := by decide +kernel
theorem subd6_3_38 : subd6_3 [2, 3] = true := by decide +kernel
theorem subd6_3_39 : subd6_3 [3] = true := by decide +kernel
theorem sbd6_3_1 : ∀ q ∈ blkd6_3_1, subd6_3 q = true := by
  unfold blkd6_3_1
  exact List.forall_mem_cons.2 ⟨subd6_3_32, List.forall_mem_cons.2 ⟨subd6_3_33, List.forall_mem_cons.2 ⟨subd6_3_34, List.forall_mem_cons.2 ⟨subd6_3_35, List.forall_mem_cons.2 ⟨subd6_3_36, List.forall_mem_cons.2 ⟨subd6_3_37, List.forall_mem_cons.2 ⟨subd6_3_38, List.forall_mem_cons.2 ⟨subd6_3_39, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_4 : ldCheck G d6_4.U d6_4.ms ldd6_4 = true := by decide +kernel
theorem pre_okd6_4 : subPre G cell6 d6_4 = true := by decide +kernel
theorem subd6_4_0 : subd6_4 [-4] = true := by decide +kernel
theorem subd6_4_1 : subd6_4 [-3] = true := by decide +kernel
theorem subd6_4_2 : subd6_4 [-2, -4] = true := by decide +kernel
theorem subd6_4_3 : subd6_4 [-2, -3] = true := by decide +kernel
theorem subd6_4_4 : subd6_4 [-2, -2] = true := by decide +kernel
theorem subd6_4_5 : subd6_4 [-2, -1] = true := by decide +kernel
theorem subd6_4_6 : subd6_4 [-2, 0] = true := by decide +kernel
theorem subd6_4_7 : subd6_4 [-2, 1] = true := by decide +kernel
theorem subd6_4_8 : subd6_4 [-2, 2] = true := by decide +kernel
theorem subd6_4_9 : subd6_4 [-2, 3] = true := by decide +kernel
theorem subd6_4_10 : subd6_4 [-1, -4] = true := by decide +kernel
theorem subd6_4_11 : subd6_4 [-1, -3] = true := by decide +kernel
theorem subd6_4_12 : subd6_4 [-1, -2] = true := by decide +kernel
theorem subd6_4_13 : subd6_4 [-1, -1] = true := by decide +kernel
theorem subd6_4_14 : subd6_4 [-1, 0] = true := by decide +kernel
theorem subd6_4_15 : subd6_4 [-1, 1] = true := by decide +kernel
theorem subd6_4_16 : subd6_4 [-1, 2] = true := by decide +kernel
theorem subd6_4_17 : subd6_4 [-1, 3] = true := by decide +kernel
theorem subd6_4_18 : subd6_4 [0, -5] = true := by decide +kernel
theorem subd6_4_19 : subd6_4 [0, -4] = true := by decide +kernel
theorem subd6_4_20 : subd6_4 [0, -3] = true := by decide +kernel
theorem subd6_4_21 : subd6_4 [0, -2] = true := by decide +kernel
theorem subd6_4_22 : subd6_4 [0, -1] = true := by decide +kernel
theorem subd6_4_23 : subd6_4 [0, 0] = true := by decide +kernel
theorem subd6_4_24 : subd6_4 [0, 1] = true := by decide +kernel
theorem subd6_4_25 : subd6_4 [0, 2] = true := by decide +kernel
theorem subd6_4_26 : subd6_4 [0, 3] = true := by decide +kernel
theorem subd6_4_27 : subd6_4 [0, 4] = true := by decide +kernel
theorem subd6_4_28 : subd6_4 [1, -4] = true := by decide +kernel
theorem subd6_4_29 : subd6_4 [1, -3] = true := by decide +kernel
theorem subd6_4_30 : subd6_4 [1, -2] = true := by decide +kernel
theorem subd6_4_31 : subd6_4 [1, -1] = true := by decide +kernel
theorem sbd6_4_0 : ∀ q ∈ blkd6_4_0, subd6_4 q = true := by
  unfold blkd6_4_0
  exact List.forall_mem_cons.2 ⟨subd6_4_0, List.forall_mem_cons.2 ⟨subd6_4_1, List.forall_mem_cons.2 ⟨subd6_4_2, List.forall_mem_cons.2 ⟨subd6_4_3, List.forall_mem_cons.2 ⟨subd6_4_4, List.forall_mem_cons.2 ⟨subd6_4_5, List.forall_mem_cons.2 ⟨subd6_4_6, List.forall_mem_cons.2 ⟨subd6_4_7, List.forall_mem_cons.2 ⟨subd6_4_8, List.forall_mem_cons.2 ⟨subd6_4_9, List.forall_mem_cons.2 ⟨subd6_4_10, List.forall_mem_cons.2 ⟨subd6_4_11, List.forall_mem_cons.2 ⟨subd6_4_12, List.forall_mem_cons.2 ⟨subd6_4_13, List.forall_mem_cons.2 ⟨subd6_4_14, List.forall_mem_cons.2 ⟨subd6_4_15, List.forall_mem_cons.2 ⟨subd6_4_16, List.forall_mem_cons.2 ⟨subd6_4_17, List.forall_mem_cons.2 ⟨subd6_4_18, List.forall_mem_cons.2 ⟨subd6_4_19, List.forall_mem_cons.2 ⟨subd6_4_20, List.forall_mem_cons.2 ⟨subd6_4_21, List.forall_mem_cons.2 ⟨subd6_4_22, List.forall_mem_cons.2 ⟨subd6_4_23, List.forall_mem_cons.2 ⟨subd6_4_24, List.forall_mem_cons.2 ⟨subd6_4_25, List.forall_mem_cons.2 ⟨subd6_4_26, List.forall_mem_cons.2 ⟨subd6_4_27, List.forall_mem_cons.2 ⟨subd6_4_28, List.forall_mem_cons.2 ⟨subd6_4_29, List.forall_mem_cons.2 ⟨subd6_4_30, List.forall_mem_cons.2 ⟨subd6_4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_4_32 : subd6_4 [1, 0] = true := by decide +kernel
theorem subd6_4_33 : subd6_4 [1, 1] = true := by decide +kernel
theorem subd6_4_34 : subd6_4 [1, 2] = true := by decide +kernel
theorem subd6_4_35 : subd6_4 [1, 3] = true := by decide +kernel
theorem subd6_4_36 : subd6_4 [2, -4] = true := by decide +kernel
theorem subd6_4_37 : subd6_4 [2, -3] = true := by decide +kernel
theorem subd6_4_38 : subd6_4 [2, -2] = true := by decide +kernel
theorem subd6_4_39 : subd6_4 [2, -1] = true := by decide +kernel
theorem subd6_4_40 : subd6_4 [2, 0] = true := by decide +kernel
theorem subd6_4_41 : subd6_4 [2, 1] = true := by decide +kernel
theorem subd6_4_42 : subd6_4 [2, 2] = true := by decide +kernel
theorem subd6_4_43 : subd6_4 [2, 3] = true := by decide +kernel
theorem subd6_4_44 : subd6_4 [3] = true := by decide +kernel
theorem subd6_4_45 : subd6_4 [4] = true := by decide +kernel
theorem sbd6_4_1 : ∀ q ∈ blkd6_4_1, subd6_4 q = true := by
  unfold blkd6_4_1
  exact List.forall_mem_cons.2 ⟨subd6_4_32, List.forall_mem_cons.2 ⟨subd6_4_33, List.forall_mem_cons.2 ⟨subd6_4_34, List.forall_mem_cons.2 ⟨subd6_4_35, List.forall_mem_cons.2 ⟨subd6_4_36, List.forall_mem_cons.2 ⟨subd6_4_37, List.forall_mem_cons.2 ⟨subd6_4_38, List.forall_mem_cons.2 ⟨subd6_4_39, List.forall_mem_cons.2 ⟨subd6_4_40, List.forall_mem_cons.2 ⟨subd6_4_41, List.forall_mem_cons.2 ⟨subd6_4_42, List.forall_mem_cons.2 ⟨subd6_4_43, List.forall_mem_cons.2 ⟨subd6_4_44, List.forall_mem_cons.2 ⟨subd6_4_45, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_5 : ldCheck G d6_5.U d6_5.ms ldd6_5 = true := by decide +kernel
theorem pre_okd6_5 : subPre G cell6 d6_5 = true := by decide +kernel
theorem subd6_5_0 : subd6_5 [-2] = true := by decide +kernel
theorem subd6_5_1 : subd6_5 [-1] = true := by decide +kernel
theorem subd6_5_2 : subd6_5 [0] = true := by decide +kernel
theorem subd6_5_3 : subd6_5 [1] = true := by decide +kernel
theorem subd6_5_4 : subd6_5 [2] = true := by decide +kernel
theorem sbd6_5_0 : ∀ q ∈ blkd6_5_0, subd6_5 q = true := by
  unfold blkd6_5_0
  exact List.forall_mem_cons.2 ⟨subd6_5_0, List.forall_mem_cons.2 ⟨subd6_5_1, List.forall_mem_cons.2 ⟨subd6_5_2, List.forall_mem_cons.2 ⟨subd6_5_3, List.forall_mem_cons.2 ⟨subd6_5_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd7_0 : ldCheck G d7_0.U d7_0.ms ldd7_0 = true := by decide +kernel
theorem pre_okd7_0 : subPre G cell7 d7_0 = true := by decide +kernel
theorem subd7_0_0 : subd7_0 [-2] = true := by decide +kernel
theorem subd7_0_1 : subd7_0 [-1] = true := by decide +kernel
theorem subd7_0_2 : subd7_0 [0] = true := by decide +kernel
theorem subd7_0_3 : subd7_0 [1] = true := by decide +kernel
theorem subd7_0_4 : subd7_0 [2] = true := by decide +kernel
theorem sbd7_0_0 : ∀ q ∈ blkd7_0_0, subd7_0 q = true := by
  unfold blkd7_0_0
  exact List.forall_mem_cons.2 ⟨subd7_0_0, List.forall_mem_cons.2 ⟨subd7_0_1, List.forall_mem_cons.2 ⟨subd7_0_2, List.forall_mem_cons.2 ⟨subd7_0_3, List.forall_mem_cons.2 ⟨subd7_0_4, List.forall_mem_nil _⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C140
