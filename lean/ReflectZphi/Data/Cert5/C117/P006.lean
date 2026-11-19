import ReflectZphi.Data.Cert5.C117.Base

namespace ReflectZphi.Data.Cert5.C117

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_3_0 : subd6_3 [-1] = true := by decide +kernel
theorem subd6_3_1 : subd6_3 [0, -2] = true := by decide +kernel
theorem subd6_3_2 : subd6_3 [0, -1] = true := by decide +kernel
theorem subd6_3_3 : subd6_3 [0, 0, -10] = true := by decide +kernel
theorem subd6_3_4 : subd6_3 [0, 0, -9] = true := by decide +kernel
theorem subd6_3_5 : subd6_3 [0, 0, -8] = true := by decide +kernel
theorem subd6_3_6 : subd6_3 [0, 0, -7] = true := by decide +kernel
theorem subd6_3_7 : subd6_3 [0, 0, -6] = true := by decide +kernel
theorem subd6_3_8 : subd6_3 [0, 0, -5] = true := by decide +kernel
theorem subd6_3_9 : subd6_3 [0, 0, -4] = true := by decide +kernel
theorem subd6_3_10 : subd6_3 [0, 0, -3] = true := by decide +kernel
theorem subd6_3_11 : subd6_3 [0, 0, -2] = true := by decide +kernel
theorem subd6_3_12 : subd6_3 [0, 0, -1] = true := by decide +kernel
theorem subd6_3_13 : subd6_3 [0, 0, 0] = true := by decide +kernel
theorem subd6_3_14 : subd6_3 [0, 0, 1] = true := by decide +kernel
theorem subd6_3_15 : subd6_3 [0, 0, 2] = true := by decide +kernel
theorem subd6_3_16 : subd6_3 [0, 0, 3] = true := by decide +kernel
theorem subd6_3_17 : subd6_3 [0, 0, 4] = true := by decide +kernel
theorem subd6_3_18 : subd6_3 [0, 0, 5] = true := by decide +kernel
theorem subd6_3_19 : subd6_3 [0, 0, 6] = true := by decide +kernel
theorem subd6_3_20 : subd6_3 [0, 0, 7] = true := by decide +kernel
theorem subd6_3_21 : subd6_3 [0, 0, 8] = true := by decide +kernel
theorem subd6_3_22 : subd6_3 [0, 0, 9] = true := by decide +kernel
theorem subd6_3_23 : subd6_3 [0, 1] = true := by decide +kernel
theorem subd6_3_24 : subd6_3 [1] = true := by decide +kernel
theorem sbd6_3_0 : ∀ q ∈ blkd6_3_0, subd6_3 q = true := by
  unfold blkd6_3_0
  exact List.forall_mem_cons.2 ⟨subd6_3_0, List.forall_mem_cons.2 ⟨subd6_3_1, List.forall_mem_cons.2 ⟨subd6_3_2, List.forall_mem_cons.2 ⟨subd6_3_3, List.forall_mem_cons.2 ⟨subd6_3_4, List.forall_mem_cons.2 ⟨subd6_3_5, List.forall_mem_cons.2 ⟨subd6_3_6, List.forall_mem_cons.2 ⟨subd6_3_7, List.forall_mem_cons.2 ⟨subd6_3_8, List.forall_mem_cons.2 ⟨subd6_3_9, List.forall_mem_cons.2 ⟨subd6_3_10, List.forall_mem_cons.2 ⟨subd6_3_11, List.forall_mem_cons.2 ⟨subd6_3_12, List.forall_mem_cons.2 ⟨subd6_3_13, List.forall_mem_cons.2 ⟨subd6_3_14, List.forall_mem_cons.2 ⟨subd6_3_15, List.forall_mem_cons.2 ⟨subd6_3_16, List.forall_mem_cons.2 ⟨subd6_3_17, List.forall_mem_cons.2 ⟨subd6_3_18, List.forall_mem_cons.2 ⟨subd6_3_19, List.forall_mem_cons.2 ⟨subd6_3_20, List.forall_mem_cons.2 ⟨subd6_3_21, List.forall_mem_cons.2 ⟨subd6_3_22, List.forall_mem_cons.2 ⟨subd6_3_23, List.forall_mem_cons.2 ⟨subd6_3_24, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_0 : ldCheck G d7_0.U d7_0.ms ldd7_0 = true := by decide +kernel
theorem pre_okd7_0 : subPre G cell7 d7_0 = true := by decide +kernel
theorem subd7_0_0 : subd7_0 [] = true := by decide +kernel
theorem sbd7_0_0 : ∀ q ∈ blkd7_0_0, subd7_0 q = true := by
  unfold blkd7_0_0
  exact List.forall_mem_cons.2 ⟨subd7_0_0, List.forall_mem_nil _⟩
theorem ld_okd7_1 : ldCheck G d7_1.U d7_1.ms ldd7_1 = true := by decide +kernel
theorem pre_okd7_1 : subPre G cell7 d7_1 = true := by decide +kernel
theorem subd7_1_0 : subd7_1 [] = true := by decide +kernel
theorem sbd7_1_0 : ∀ q ∈ blkd7_1_0, subd7_1 q = true := by
  unfold blkd7_1_0
  exact List.forall_mem_cons.2 ⟨subd7_1_0, List.forall_mem_nil _⟩
theorem ld_okd7_2 : ldCheck G d7_2.U d7_2.ms ldd7_2 = true := by decide +kernel
theorem pre_okd7_2 : subPre G cell7 d7_2 = true := by decide +kernel
theorem subd7_2_0 : subd7_2 [-2, -2] = true := by decide +kernel
theorem subd7_2_1 : subd7_2 [-2, -1] = true := by decide +kernel
theorem subd7_2_2 : subd7_2 [-2, 0] = true := by decide +kernel
theorem subd7_2_3 : subd7_2 [-2, 1] = true := by decide +kernel
theorem subd7_2_4 : subd7_2 [-1, -3] = true := by decide +kernel
theorem subd7_2_5 : subd7_2 [-1, -2] = true := by decide +kernel
theorem subd7_2_6 : subd7_2 [-1, -1] = true := by decide +kernel
theorem subd7_2_7 : subd7_2 [-1, 0] = true := by decide +kernel
theorem subd7_2_8 : subd7_2 [-1, 1] = true := by decide +kernel
theorem subd7_2_9 : subd7_2 [-1, 2] = true := by decide +kernel
theorem subd7_2_10 : subd7_2 [0, -3] = true := by decide +kernel
theorem subd7_2_11 : subd7_2 [0, -2] = true := by decide +kernel
theorem subd7_2_12 : subd7_2 [0, -1] = true := by decide +kernel
theorem subd7_2_13 : subd7_2 [0, 0, -7] = true := by decide +kernel
theorem subd7_2_14 : subd7_2 [0, 0, -6] = true := by decide +kernel
theorem subd7_2_15 : subd7_2 [0, 0, -5] = true := by decide +kernel
theorem subd7_2_16 : subd7_2 [0, 0, -4] = true := by decide +kernel
theorem subd7_2_17 : subd7_2 [0, 0, -3] = true := by decide +kernel
theorem subd7_2_18 : subd7_2 [0, 0, -2] = true := by decide +kernel
theorem subd7_2_19 : subd7_2 [0, 0, -1] = true := by decide +kernel
theorem subd7_2_20 : subd7_2 [0, 0, 0] = true := by decide +kernel
theorem subd7_2_21 : subd7_2 [0, 0, 1] = true := by decide +kernel
theorem subd7_2_22 : subd7_2 [0, 0, 2] = true := by decide +kernel
theorem subd7_2_23 : subd7_2 [0, 0, 3] = true := by decide +kernel
theorem subd7_2_24 : subd7_2 [0, 0, 4] = true := by decide +kernel
theorem subd7_2_25 : subd7_2 [0, 0, 5] = true := by decide +kernel
theorem subd7_2_26 : subd7_2 [0, 0, 6] = true := by decide +kernel
theorem subd7_2_27 : subd7_2 [0, 1] = true := by decide +kernel
theorem subd7_2_28 : subd7_2 [0, 2] = true := by decide +kernel
theorem subd7_2_29 : subd7_2 [1, -3] = true := by decide +kernel
theorem subd7_2_30 : subd7_2 [1, -2] = true := by decide +kernel
theorem subd7_2_31 : subd7_2 [1, -1] = true := by decide +kernel
theorem sbd7_2_0 : ∀ q ∈ blkd7_2_0, subd7_2 q = true := by
  unfold blkd7_2_0
  exact List.forall_mem_cons.2 ⟨subd7_2_0, List.forall_mem_cons.2 ⟨subd7_2_1, List.forall_mem_cons.2 ⟨subd7_2_2, List.forall_mem_cons.2 ⟨subd7_2_3, List.forall_mem_cons.2 ⟨subd7_2_4, List.forall_mem_cons.2 ⟨subd7_2_5, List.forall_mem_cons.2 ⟨subd7_2_6, List.forall_mem_cons.2 ⟨subd7_2_7, List.forall_mem_cons.2 ⟨subd7_2_8, List.forall_mem_cons.2 ⟨subd7_2_9, List.forall_mem_cons.2 ⟨subd7_2_10, List.forall_mem_cons.2 ⟨subd7_2_11, List.forall_mem_cons.2 ⟨subd7_2_12, List.forall_mem_cons.2 ⟨subd7_2_13, List.forall_mem_cons.2 ⟨subd7_2_14, List.forall_mem_cons.2 ⟨subd7_2_15, List.forall_mem_cons.2 ⟨subd7_2_16, List.forall_mem_cons.2 ⟨subd7_2_17, List.forall_mem_cons.2 ⟨subd7_2_18, List.forall_mem_cons.2 ⟨subd7_2_19, List.forall_mem_cons.2 ⟨subd7_2_20, List.forall_mem_cons.2 ⟨subd7_2_21, List.forall_mem_cons.2 ⟨subd7_2_22, List.forall_mem_cons.2 ⟨subd7_2_23, List.forall_mem_cons.2 ⟨subd7_2_24, List.forall_mem_cons.2 ⟨subd7_2_25, List.forall_mem_cons.2 ⟨subd7_2_26, List.forall_mem_cons.2 ⟨subd7_2_27, List.forall_mem_cons.2 ⟨subd7_2_28, List.forall_mem_cons.2 ⟨subd7_2_29, List.forall_mem_cons.2 ⟨subd7_2_30, List.forall_mem_cons.2 ⟨subd7_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_32 : subd7_2 [1, 0] = true := by decide +kernel
theorem subd7_2_33 : subd7_2 [1, 1] = true := by decide +kernel
theorem subd7_2_34 : subd7_2 [1, 2] = true := by decide +kernel
theorem subd7_2_35 : subd7_2 [2, -2] = true := by decide +kernel
theorem subd7_2_36 : subd7_2 [2, -1] = true := by decide +kernel
theorem subd7_2_37 : subd7_2 [2, 0] = true := by decide +kernel
theorem subd7_2_38 : subd7_2 [2, 1] = true := by decide +kernel
theorem sbd7_2_1 : ∀ q ∈ blkd7_2_1, subd7_2 q = true := by
  unfold blkd7_2_1
  exact List.forall_mem_cons.2 ⟨subd7_2_32, List.forall_mem_cons.2 ⟨subd7_2_33, List.forall_mem_cons.2 ⟨subd7_2_34, List.forall_mem_cons.2 ⟨subd7_2_35, List.forall_mem_cons.2 ⟨subd7_2_36, List.forall_mem_cons.2 ⟨subd7_2_37, List.forall_mem_cons.2 ⟨subd7_2_38, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_3 : ldCheck G d7_3.U d7_3.ms ldd7_3 = true := by decide +kernel
theorem pre_okd7_3 : subPre G cell7 d7_3 = true := by decide +kernel
theorem subd7_3_0 : subd7_3 [-1] = true := by decide +kernel
theorem subd7_3_1 : subd7_3 [0, -2] = true := by decide +kernel
theorem subd7_3_2 : subd7_3 [0, -1] = true := by decide +kernel
theorem subd7_3_3 : subd7_3 [0, 0, -9] = true := by decide +kernel
theorem subd7_3_4 : subd7_3 [0, 0, -8] = true := by decide +kernel
theorem subd7_3_5 : subd7_3 [0, 0, -7] = true := by decide +kernel
theorem subd7_3_6 : subd7_3 [0, 0, -6] = true := by decide +kernel
theorem subd7_3_7 : subd7_3 [0, 0, -5] = true := by decide +kernel
theorem subd7_3_8 : subd7_3 [0, 0, -4] = true := by decide +kernel
theorem subd7_3_9 : subd7_3 [0, 0, -3] = true := by decide +kernel
theorem subd7_3_10 : subd7_3 [0, 0, -2] = true := by decide +kernel
theorem subd7_3_11 : subd7_3 [0, 0, -1] = true := by decide +kernel
theorem subd7_3_12 : subd7_3 [0, 0, 0] = true := by decide +kernel
theorem subd7_3_13 : subd7_3 [0, 0, 1] = true := by decide +kernel
theorem subd7_3_14 : subd7_3 [0, 0, 2] = true := by decide +kernel
theorem subd7_3_15 : subd7_3 [0, 0, 3] = true := by decide +kernel
theorem subd7_3_16 : subd7_3 [0, 0, 4] = true := by decide +kernel
theorem subd7_3_17 : subd7_3 [0, 0, 5] = true := by decide +kernel
theorem subd7_3_18 : subd7_3 [0, 0, 6] = true := by decide +kernel
theorem subd7_3_19 : subd7_3 [0, 0, 7] = true := by decide +kernel
theorem subd7_3_20 : subd7_3 [0, 0, 8] = true := by decide +kernel
theorem subd7_3_21 : subd7_3 [0, 1] = true := by decide +kernel
theorem subd7_3_22 : subd7_3 [1] = true := by decide +kernel
theorem sbd7_3_0 : ∀ q ∈ blkd7_3_0, subd7_3 q = true := by
  unfold blkd7_3_0
  exact List.forall_mem_cons.2 ⟨subd7_3_0, List.forall_mem_cons.2 ⟨subd7_3_1, List.forall_mem_cons.2 ⟨subd7_3_2, List.forall_mem_cons.2 ⟨subd7_3_3, List.forall_mem_cons.2 ⟨subd7_3_4, List.forall_mem_cons.2 ⟨subd7_3_5, List.forall_mem_cons.2 ⟨subd7_3_6, List.forall_mem_cons.2 ⟨subd7_3_7, List.forall_mem_cons.2 ⟨subd7_3_8, List.forall_mem_cons.2 ⟨subd7_3_9, List.forall_mem_cons.2 ⟨subd7_3_10, List.forall_mem_cons.2 ⟨subd7_3_11, List.forall_mem_cons.2 ⟨subd7_3_12, List.forall_mem_cons.2 ⟨subd7_3_13, List.forall_mem_cons.2 ⟨subd7_3_14, List.forall_mem_cons.2 ⟨subd7_3_15, List.forall_mem_cons.2 ⟨subd7_3_16, List.forall_mem_cons.2 ⟨subd7_3_17, List.forall_mem_cons.2 ⟨subd7_3_18, List.forall_mem_cons.2 ⟨subd7_3_19, List.forall_mem_cons.2 ⟨subd7_3_20, List.forall_mem_cons.2 ⟨subd7_3_21, List.forall_mem_cons.2 ⟨subd7_3_22, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_0 : ldCheck G d8_0.U d8_0.ms ldd8_0 = true := by decide +kernel
theorem pre_okd8_0 : subPre G cell8 d8_0 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C117
