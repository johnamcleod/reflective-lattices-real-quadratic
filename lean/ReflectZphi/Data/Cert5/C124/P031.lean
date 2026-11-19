import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd7_3 : ldCheck G d7_3.U d7_3.ms ldd7_3 = true := by decide +kernel
theorem pre_okd7_3 : subPre G cell7 d7_3 = true := by decide +kernel
theorem subd7_3_0 : subd7_3 [-3] = true := by decide +kernel
theorem subd7_3_1 : subd7_3 [-2] = true := by decide +kernel
theorem subd7_3_2 : subd7_3 [-1, -4] = true := by decide +kernel
theorem subd7_3_3 : subd7_3 [-1, -3] = true := by decide +kernel
theorem subd7_3_4 : subd7_3 [-1, -2] = true := by decide +kernel
theorem subd7_3_5 : subd7_3 [-1, -1] = true := by decide +kernel
theorem subd7_3_6 : subd7_3 [-1, 0] = true := by decide +kernel
theorem subd7_3_7 : subd7_3 [-1, 1] = true := by decide +kernel
theorem subd7_3_8 : subd7_3 [-1, 2] = true := by decide +kernel
theorem subd7_3_9 : subd7_3 [0, -4] = true := by decide +kernel
theorem subd7_3_10 : subd7_3 [0, -3] = true := by decide +kernel
theorem subd7_3_11 : subd7_3 [0, -2] = true := by decide +kernel
theorem subd7_3_12 : subd7_3 [0, -1] = true := by decide +kernel
theorem subd7_3_13 : subd7_3 [0, 0] = true := by decide +kernel
theorem subd7_3_14 : subd7_3 [0, 1] = true := by decide +kernel
theorem subd7_3_15 : subd7_3 [0, 2] = true := by decide +kernel
theorem subd7_3_16 : subd7_3 [0, 3] = true := by decide +kernel
theorem subd7_3_17 : subd7_3 [1, -3] = true := by decide +kernel
theorem subd7_3_18 : subd7_3 [1, -2] = true := by decide +kernel
theorem subd7_3_19 : subd7_3 [1, -1] = true := by decide +kernel
theorem subd7_3_20 : subd7_3 [1, 0] = true := by decide +kernel
theorem subd7_3_21 : subd7_3 [1, 1] = true := by decide +kernel
theorem subd7_3_22 : subd7_3 [1, 2] = true := by decide +kernel
theorem subd7_3_23 : subd7_3 [1, 3] = true := by decide +kernel
theorem subd7_3_24 : subd7_3 [2] = true := by decide +kernel
theorem subd7_3_25 : subd7_3 [3] = true := by decide +kernel
theorem sbd7_3_0 : ∀ q ∈ blkd7_3_0, subd7_3 q = true := by
  unfold blkd7_3_0
  exact List.forall_mem_cons.2 ⟨subd7_3_0, List.forall_mem_cons.2 ⟨subd7_3_1, List.forall_mem_cons.2 ⟨subd7_3_2, List.forall_mem_cons.2 ⟨subd7_3_3, List.forall_mem_cons.2 ⟨subd7_3_4, List.forall_mem_cons.2 ⟨subd7_3_5, List.forall_mem_cons.2 ⟨subd7_3_6, List.forall_mem_cons.2 ⟨subd7_3_7, List.forall_mem_cons.2 ⟨subd7_3_8, List.forall_mem_cons.2 ⟨subd7_3_9, List.forall_mem_cons.2 ⟨subd7_3_10, List.forall_mem_cons.2 ⟨subd7_3_11, List.forall_mem_cons.2 ⟨subd7_3_12, List.forall_mem_cons.2 ⟨subd7_3_13, List.forall_mem_cons.2 ⟨subd7_3_14, List.forall_mem_cons.2 ⟨subd7_3_15, List.forall_mem_cons.2 ⟨subd7_3_16, List.forall_mem_cons.2 ⟨subd7_3_17, List.forall_mem_cons.2 ⟨subd7_3_18, List.forall_mem_cons.2 ⟨subd7_3_19, List.forall_mem_cons.2 ⟨subd7_3_20, List.forall_mem_cons.2 ⟨subd7_3_21, List.forall_mem_cons.2 ⟨subd7_3_22, List.forall_mem_cons.2 ⟨subd7_3_23, List.forall_mem_cons.2 ⟨subd7_3_24, List.forall_mem_cons.2 ⟨subd7_3_25, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_4 : ldCheck G d7_4.U d7_4.ms ldd7_4 = true := by decide +kernel
theorem pre_okd7_4 : subPre G cell7 d7_4 = true := by decide +kernel
theorem subd7_4_0 : subd7_4 [-3] = true := by decide +kernel
theorem subd7_4_1 : subd7_4 [-2] = true := by decide +kernel
theorem subd7_4_2 : subd7_4 [-1] = true := by decide +kernel
theorem subd7_4_3 : subd7_4 [0] = true := by decide +kernel
theorem subd7_4_4 : subd7_4 [1] = true := by decide +kernel
theorem subd7_4_5 : subd7_4 [2] = true := by decide +kernel
theorem subd7_4_6 : subd7_4 [3] = true := by decide +kernel
theorem sbd7_4_0 : ∀ q ∈ blkd7_4_0, subd7_4 q = true := by
  unfold blkd7_4_0
  exact List.forall_mem_cons.2 ⟨subd7_4_0, List.forall_mem_cons.2 ⟨subd7_4_1, List.forall_mem_cons.2 ⟨subd7_4_2, List.forall_mem_cons.2 ⟨subd7_4_3, List.forall_mem_cons.2 ⟨subd7_4_4, List.forall_mem_cons.2 ⟨subd7_4_5, List.forall_mem_cons.2 ⟨subd7_4_6, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_5 : ldCheck G d7_5.U d7_5.ms ldd7_5 = true := by decide +kernel
theorem pre_okd7_5 : subPre G cell7 d7_5 = true := by decide +kernel
theorem subd7_5_0 : subd7_5 [-3] = true := by decide +kernel
theorem subd7_5_1 : subd7_5 [-2] = true := by decide +kernel
theorem subd7_5_2 : subd7_5 [-1] = true := by decide +kernel
theorem subd7_5_3 : subd7_5 [0, -3] = true := by decide +kernel
theorem subd7_5_4 : subd7_5 [0, -2] = true := by decide +kernel
theorem subd7_5_5 : subd7_5 [0, -1] = true := by decide +kernel
theorem subd7_5_6 : subd7_5 [0, 0] = true := by decide +kernel
theorem subd7_5_7 : subd7_5 [0, 1] = true := by decide +kernel
theorem subd7_5_8 : subd7_5 [0, 2] = true := by decide +kernel
theorem subd7_5_9 : subd7_5 [1] = true := by decide +kernel
theorem subd7_5_10 : subd7_5 [2] = true := by decide +kernel
theorem subd7_5_11 : subd7_5 [3] = true := by decide +kernel
theorem sbd7_5_0 : ∀ q ∈ blkd7_5_0, subd7_5 q = true := by
  unfold blkd7_5_0
  exact List.forall_mem_cons.2 ⟨subd7_5_0, List.forall_mem_cons.2 ⟨subd7_5_1, List.forall_mem_cons.2 ⟨subd7_5_2, List.forall_mem_cons.2 ⟨subd7_5_3, List.forall_mem_cons.2 ⟨subd7_5_4, List.forall_mem_cons.2 ⟨subd7_5_5, List.forall_mem_cons.2 ⟨subd7_5_6, List.forall_mem_cons.2 ⟨subd7_5_7, List.forall_mem_cons.2 ⟨subd7_5_8, List.forall_mem_cons.2 ⟨subd7_5_9, List.forall_mem_cons.2 ⟨subd7_5_10, List.forall_mem_cons.2 ⟨subd7_5_11, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_6 : ldCheck G d7_6.U d7_6.ms ldd7_6 = true := by decide +kernel
theorem pre_okd7_6 : subPre G cell7 d7_6 = true := by decide +kernel
theorem subd7_6_0 : subd7_6 [-5] = true := by decide +kernel
theorem subd7_6_1 : subd7_6 [-4, -3] = true := by decide +kernel
theorem subd7_6_2 : subd7_6 [-4, -2] = true := by decide +kernel
theorem subd7_6_3 : subd7_6 [-4, -1] = true := by decide +kernel
theorem subd7_6_4 : subd7_6 [-4, 0] = true := by decide +kernel
theorem subd7_6_5 : subd7_6 [-4, 1] = true := by decide +kernel
theorem subd7_6_6 : subd7_6 [-4, 2] = true := by decide +kernel
theorem subd7_6_7 : subd7_6 [-4, 3] = true := by decide +kernel
theorem subd7_6_8 : subd7_6 [-4, 4] = true := by decide +kernel
theorem subd7_6_9 : subd7_6 [-3, -4] = true := by decide +kernel
theorem subd7_6_10 : subd7_6 [-3, -3] = true := by decide +kernel
theorem subd7_6_11 : subd7_6 [-3, -2] = true := by decide +kernel
theorem subd7_6_12 : subd7_6 [-3, -1] = true := by decide +kernel
theorem subd7_6_13 : subd7_6 [-3, 0] = true := by decide +kernel
theorem subd7_6_14 : subd7_6 [-3, 1] = true := by decide +kernel
theorem subd7_6_15 : subd7_6 [-3, 2] = true := by decide +kernel
theorem subd7_6_16 : subd7_6 [-3, 3] = true := by decide +kernel
theorem subd7_6_17 : subd7_6 [-3, 4] = true := by decide +kernel
theorem subd7_6_18 : subd7_6 [-3, 5] = true := by decide +kernel
theorem subd7_6_19 : subd7_6 [-2, -5] = true := by decide +kernel
theorem subd7_6_20 : subd7_6 [-2, -4] = true := by decide +kernel
theorem subd7_6_21 : subd7_6 [-2, -3] = true := by decide +kernel
theorem subd7_6_22 : subd7_6 [-2, -2] = true := by decide +kernel
theorem subd7_6_23 : subd7_6 [-2, -1] = true := by decide +kernel
theorem subd7_6_24 : subd7_6 [-2, 0] = true := by decide +kernel
theorem subd7_6_25 : subd7_6 [-2, 1] = true := by decide +kernel
theorem subd7_6_26 : subd7_6 [-2, 2] = true := by decide +kernel
theorem subd7_6_27 : subd7_6 [-2, 3] = true := by decide +kernel
theorem subd7_6_28 : subd7_6 [-2, 4] = true := by decide +kernel
theorem subd7_6_29 : subd7_6 [-2, 5] = true := by decide +kernel
theorem subd7_6_30 : subd7_6 [-1, -6] = true := by decide +kernel
theorem subd7_6_31 : subd7_6 [-1, -5] = true := by decide +kernel
theorem sbd7_6_0 : ∀ q ∈ blkd7_6_0, subd7_6 q = true := by
  unfold blkd7_6_0
  exact List.forall_mem_cons.2 ⟨subd7_6_0, List.forall_mem_cons.2 ⟨subd7_6_1, List.forall_mem_cons.2 ⟨subd7_6_2, List.forall_mem_cons.2 ⟨subd7_6_3, List.forall_mem_cons.2 ⟨subd7_6_4, List.forall_mem_cons.2 ⟨subd7_6_5, List.forall_mem_cons.2 ⟨subd7_6_6, List.forall_mem_cons.2 ⟨subd7_6_7, List.forall_mem_cons.2 ⟨subd7_6_8, List.forall_mem_cons.2 ⟨subd7_6_9, List.forall_mem_cons.2 ⟨subd7_6_10, List.forall_mem_cons.2 ⟨subd7_6_11, List.forall_mem_cons.2 ⟨subd7_6_12, List.forall_mem_cons.2 ⟨subd7_6_13, List.forall_mem_cons.2 ⟨subd7_6_14, List.forall_mem_cons.2 ⟨subd7_6_15, List.forall_mem_cons.2 ⟨subd7_6_16, List.forall_mem_cons.2 ⟨subd7_6_17, List.forall_mem_cons.2 ⟨subd7_6_18, List.forall_mem_cons.2 ⟨subd7_6_19, List.forall_mem_cons.2 ⟨subd7_6_20, List.forall_mem_cons.2 ⟨subd7_6_21, List.forall_mem_cons.2 ⟨subd7_6_22, List.forall_mem_cons.2 ⟨subd7_6_23, List.forall_mem_cons.2 ⟨subd7_6_24, List.forall_mem_cons.2 ⟨subd7_6_25, List.forall_mem_cons.2 ⟨subd7_6_26, List.forall_mem_cons.2 ⟨subd7_6_27, List.forall_mem_cons.2 ⟨subd7_6_28, List.forall_mem_cons.2 ⟨subd7_6_29, List.forall_mem_cons.2 ⟨subd7_6_30, List.forall_mem_cons.2 ⟨subd7_6_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C124
