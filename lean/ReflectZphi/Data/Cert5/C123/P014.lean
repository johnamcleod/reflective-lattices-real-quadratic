import ReflectZphi.Data.Cert5.C123.Base

namespace ReflectZphi.Data.Cert5.C123

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_6_0 : subd6_6 [-2, -3] = true := by decide +kernel
theorem subd6_6_1 : subd6_6 [-2, -2] = true := by decide +kernel
theorem subd6_6_2 : subd6_6 [-2, -1] = true := by decide +kernel
theorem subd6_6_3 : subd6_6 [-2, 0] = true := by decide +kernel
theorem subd6_6_4 : subd6_6 [-2, 1] = true := by decide +kernel
theorem subd6_6_5 : subd6_6 [-2, 2] = true := by decide +kernel
theorem subd6_6_6 : subd6_6 [-1, -3] = true := by decide +kernel
theorem subd6_6_7 : subd6_6 [-1, -2] = true := by decide +kernel
theorem subd6_6_8 : subd6_6 [-1, -1] = true := by decide +kernel
theorem subd6_6_9 : subd6_6 [-1, 0] = true := by decide +kernel
theorem subd6_6_10 : subd6_6 [-1, 1] = true := by decide +kernel
theorem subd6_6_11 : subd6_6 [-1, 2] = true := by decide +kernel
theorem subd6_6_12 : subd6_6 [0, -4] = true := by decide +kernel
theorem subd6_6_13 : subd6_6 [0, -3] = true := by decide +kernel
theorem subd6_6_14 : subd6_6 [0, -2] = true := by decide +kernel
theorem subd6_6_15 : subd6_6 [0, -1] = true := by decide +kernel
theorem subd6_6_16 : subd6_6 [0, 0, -7] = true := by decide +kernel
theorem subd6_6_17 : subd6_6 [0, 0, -6] = true := by decide +kernel
theorem subd6_6_18 : subd6_6 [0, 0, -5] = true := by decide +kernel
theorem subd6_6_19 : subd6_6 [0, 0, -4] = true := by decide +kernel
theorem subd6_6_20 : subd6_6 [0, 0, -3] = true := by decide +kernel
theorem subd6_6_21 : subd6_6 [0, 0, -2] = true := by decide +kernel
theorem subd6_6_22 : subd6_6 [0, 0, -1] = true := by decide +kernel
theorem subd6_6_23 : subd6_6 [0, 0, 0] = true := by decide +kernel
theorem subd6_6_24 : subd6_6 [0, 0, 1] = true := by decide +kernel
theorem subd6_6_25 : subd6_6 [0, 0, 2] = true := by decide +kernel
theorem subd6_6_26 : subd6_6 [0, 0, 3] = true := by decide +kernel
theorem subd6_6_27 : subd6_6 [0, 0, 4] = true := by decide +kernel
theorem subd6_6_28 : subd6_6 [0, 0, 5] = true := by decide +kernel
theorem subd6_6_29 : subd6_6 [0, 0, 6] = true := by decide +kernel
theorem subd6_6_30 : subd6_6 [0, 1] = true := by decide +kernel
theorem subd6_6_31 : subd6_6 [0, 2] = true := by decide +kernel
theorem sbd6_6_0 : ∀ q ∈ blkd6_6_0, subd6_6 q = true := by
  unfold blkd6_6_0
  exact List.forall_mem_cons.2 ⟨subd6_6_0, List.forall_mem_cons.2 ⟨subd6_6_1, List.forall_mem_cons.2 ⟨subd6_6_2, List.forall_mem_cons.2 ⟨subd6_6_3, List.forall_mem_cons.2 ⟨subd6_6_4, List.forall_mem_cons.2 ⟨subd6_6_5, List.forall_mem_cons.2 ⟨subd6_6_6, List.forall_mem_cons.2 ⟨subd6_6_7, List.forall_mem_cons.2 ⟨subd6_6_8, List.forall_mem_cons.2 ⟨subd6_6_9, List.forall_mem_cons.2 ⟨subd6_6_10, List.forall_mem_cons.2 ⟨subd6_6_11, List.forall_mem_cons.2 ⟨subd6_6_12, List.forall_mem_cons.2 ⟨subd6_6_13, List.forall_mem_cons.2 ⟨subd6_6_14, List.forall_mem_cons.2 ⟨subd6_6_15, List.forall_mem_cons.2 ⟨subd6_6_16, List.forall_mem_cons.2 ⟨subd6_6_17, List.forall_mem_cons.2 ⟨subd6_6_18, List.forall_mem_cons.2 ⟨subd6_6_19, List.forall_mem_cons.2 ⟨subd6_6_20, List.forall_mem_cons.2 ⟨subd6_6_21, List.forall_mem_cons.2 ⟨subd6_6_22, List.forall_mem_cons.2 ⟨subd6_6_23, List.forall_mem_cons.2 ⟨subd6_6_24, List.forall_mem_cons.2 ⟨subd6_6_25, List.forall_mem_cons.2 ⟨subd6_6_26, List.forall_mem_cons.2 ⟨subd6_6_27, List.forall_mem_cons.2 ⟨subd6_6_28, List.forall_mem_cons.2 ⟨subd6_6_29, List.forall_mem_cons.2 ⟨subd6_6_30, List.forall_mem_cons.2 ⟨subd6_6_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_6_32 : subd6_6 [0, 3] = true := by decide +kernel
theorem subd6_6_33 : subd6_6 [1, -3] = true := by decide +kernel
theorem subd6_6_34 : subd6_6 [1, -2] = true := by decide +kernel
theorem subd6_6_35 : subd6_6 [1, -1] = true := by decide +kernel
theorem subd6_6_36 : subd6_6 [1, 0] = true := by decide +kernel
theorem subd6_6_37 : subd6_6 [1, 1] = true := by decide +kernel
theorem subd6_6_38 : subd6_6 [1, 2] = true := by decide +kernel
theorem subd6_6_39 : subd6_6 [2, -3] = true := by decide +kernel
theorem subd6_6_40 : subd6_6 [2, -2] = true := by decide +kernel
theorem subd6_6_41 : subd6_6 [2, -1] = true := by decide +kernel
theorem subd6_6_42 : subd6_6 [2, 0] = true := by decide +kernel
theorem subd6_6_43 : subd6_6 [2, 1] = true := by decide +kernel
theorem subd6_6_44 : subd6_6 [2, 2] = true := by decide +kernel
theorem sbd6_6_1 : ∀ q ∈ blkd6_6_1, subd6_6 q = true := by
  unfold blkd6_6_1
  exact List.forall_mem_cons.2 ⟨subd6_6_32, List.forall_mem_cons.2 ⟨subd6_6_33, List.forall_mem_cons.2 ⟨subd6_6_34, List.forall_mem_cons.2 ⟨subd6_6_35, List.forall_mem_cons.2 ⟨subd6_6_36, List.forall_mem_cons.2 ⟨subd6_6_37, List.forall_mem_cons.2 ⟨subd6_6_38, List.forall_mem_cons.2 ⟨subd6_6_39, List.forall_mem_cons.2 ⟨subd6_6_40, List.forall_mem_cons.2 ⟨subd6_6_41, List.forall_mem_cons.2 ⟨subd6_6_42, List.forall_mem_cons.2 ⟨subd6_6_43, List.forall_mem_cons.2 ⟨subd6_6_44, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
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
theorem ld_okd7_1 : ldCheck G d7_1.U d7_1.ms ldd7_1 = true := by decide +kernel
theorem pre_okd7_1 : subPre G cell7 d7_1 = true := by decide +kernel
theorem subd7_1_0 : subd7_1 [0, -1] = true := by decide +kernel
theorem subd7_1_1 : subd7_1 [0, 0, -7] = true := by decide +kernel
theorem subd7_1_2 : subd7_1 [0, 0, -6] = true := by decide +kernel
theorem subd7_1_3 : subd7_1 [0, 0, -5] = true := by decide +kernel
theorem subd7_1_4 : subd7_1 [0, 0, -4] = true := by decide +kernel
theorem subd7_1_5 : subd7_1 [0, 0, -3] = true := by decide +kernel
theorem subd7_1_6 : subd7_1 [0, 0, -2] = true := by decide +kernel
theorem subd7_1_7 : subd7_1 [0, 0, -1] = true := by decide +kernel
theorem subd7_1_8 : subd7_1 [0, 0, 0] = true := by decide +kernel
theorem subd7_1_9 : subd7_1 [0, 0, 1] = true := by decide +kernel
theorem subd7_1_10 : subd7_1 [0, 0, 2] = true := by decide +kernel
theorem subd7_1_11 : subd7_1 [0, 0, 3] = true := by decide +kernel
theorem subd7_1_12 : subd7_1 [0, 0, 4] = true := by decide +kernel
theorem subd7_1_13 : subd7_1 [0, 0, 5] = true := by decide +kernel
theorem subd7_1_14 : subd7_1 [0, 0, 6] = true := by decide +kernel
theorem sbd7_1_0 : ∀ q ∈ blkd7_1_0, subd7_1 q = true := by
  unfold blkd7_1_0
  exact List.forall_mem_cons.2 ⟨subd7_1_0, List.forall_mem_cons.2 ⟨subd7_1_1, List.forall_mem_cons.2 ⟨subd7_1_2, List.forall_mem_cons.2 ⟨subd7_1_3, List.forall_mem_cons.2 ⟨subd7_1_4, List.forall_mem_cons.2 ⟨subd7_1_5, List.forall_mem_cons.2 ⟨subd7_1_6, List.forall_mem_cons.2 ⟨subd7_1_7, List.forall_mem_cons.2 ⟨subd7_1_8, List.forall_mem_cons.2 ⟨subd7_1_9, List.forall_mem_cons.2 ⟨subd7_1_10, List.forall_mem_cons.2 ⟨subd7_1_11, List.forall_mem_cons.2 ⟨subd7_1_12, List.forall_mem_cons.2 ⟨subd7_1_13, List.forall_mem_cons.2 ⟨subd7_1_14, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_2 : ldCheck G d7_2.U d7_2.ms ldd7_2 = true := by decide +kernel
theorem pre_okd7_2 : subPre G cell7 d7_2 = true := by decide +kernel
theorem subd7_2_0 : subd7_2 [-1, -2] = true := by decide +kernel
theorem subd7_2_1 : subd7_2 [-1, -1] = true := by decide +kernel
theorem subd7_2_2 : subd7_2 [-1, 0] = true := by decide +kernel
theorem subd7_2_3 : subd7_2 [0, -2] = true := by decide +kernel
theorem subd7_2_4 : subd7_2 [0, -1] = true := by decide +kernel
theorem subd7_2_5 : subd7_2 [0, 0, -7] = true := by decide +kernel
theorem subd7_2_6 : subd7_2 [0, 0, -6] = true := by decide +kernel
theorem subd7_2_7 : subd7_2 [0, 0, -5] = true := by decide +kernel
theorem subd7_2_8 : subd7_2 [0, 0, -4] = true := by decide +kernel
theorem subd7_2_9 : subd7_2 [0, 0, -3] = true := by decide +kernel
theorem subd7_2_10 : subd7_2 [0, 0, -2] = true := by decide +kernel
theorem subd7_2_11 : subd7_2 [0, 0, -1] = true := by decide +kernel
theorem subd7_2_12 : subd7_2 [0, 0, 0] = true := by decide +kernel
theorem subd7_2_13 : subd7_2 [0, 0, 1] = true := by decide +kernel
theorem subd7_2_14 : subd7_2 [0, 0, 2] = true := by decide +kernel
theorem subd7_2_15 : subd7_2 [0, 0, 3] = true := by decide +kernel
theorem subd7_2_16 : subd7_2 [0, 0, 4] = true := by decide +kernel
theorem subd7_2_17 : subd7_2 [0, 0, 5] = true := by decide +kernel
theorem subd7_2_18 : subd7_2 [0, 0, 6] = true := by decide +kernel
theorem subd7_2_19 : subd7_2 [0, 1] = true := by decide +kernel
theorem subd7_2_20 : subd7_2 [1, -1] = true := by decide +kernel
theorem subd7_2_21 : subd7_2 [1, 0] = true := by decide +kernel
theorem subd7_2_22 : subd7_2 [1, 1] = true := by decide +kernel
theorem sbd7_2_0 : ∀ q ∈ blkd7_2_0, subd7_2 q = true := by
  unfold blkd7_2_0
  exact List.forall_mem_cons.2 ⟨subd7_2_0, List.forall_mem_cons.2 ⟨subd7_2_1, List.forall_mem_cons.2 ⟨subd7_2_2, List.forall_mem_cons.2 ⟨subd7_2_3, List.forall_mem_cons.2 ⟨subd7_2_4, List.forall_mem_cons.2 ⟨subd7_2_5, List.forall_mem_cons.2 ⟨subd7_2_6, List.forall_mem_cons.2 ⟨subd7_2_7, List.forall_mem_cons.2 ⟨subd7_2_8, List.forall_mem_cons.2 ⟨subd7_2_9, List.forall_mem_cons.2 ⟨subd7_2_10, List.forall_mem_cons.2 ⟨subd7_2_11, List.forall_mem_cons.2 ⟨subd7_2_12, List.forall_mem_cons.2 ⟨subd7_2_13, List.forall_mem_cons.2 ⟨subd7_2_14, List.forall_mem_cons.2 ⟨subd7_2_15, List.forall_mem_cons.2 ⟨subd7_2_16, List.forall_mem_cons.2 ⟨subd7_2_17, List.forall_mem_cons.2 ⟨subd7_2_18, List.forall_mem_cons.2 ⟨subd7_2_19, List.forall_mem_cons.2 ⟨subd7_2_20, List.forall_mem_cons.2 ⟨subd7_2_21, List.forall_mem_cons.2 ⟨subd7_2_22, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_3 : ldCheck G d7_3.U d7_3.ms ldd7_3 = true := by decide +kernel
theorem pre_okd7_3 : subPre G cell7 d7_3 = true := by decide +kernel
theorem subd7_3_0 : subd7_3 [-1] = true := by decide +kernel
theorem subd7_3_1 : subd7_3 [0] = true := by decide +kernel
theorem subd7_3_2 : subd7_3 [1] = true := by decide +kernel
theorem sbd7_3_0 : ∀ q ∈ blkd7_3_0, subd7_3 q = true := by
  unfold blkd7_3_0
  exact List.forall_mem_cons.2 ⟨subd7_3_0, List.forall_mem_cons.2 ⟨subd7_3_1, List.forall_mem_cons.2 ⟨subd7_3_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd7_4 : ldCheck G d7_4.U d7_4.ms ldd7_4 = true := by decide +kernel
theorem pre_okd7_4 : subPre G cell7 d7_4 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C123
