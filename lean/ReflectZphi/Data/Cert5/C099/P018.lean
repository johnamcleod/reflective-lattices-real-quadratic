import ReflectZphi.Data.Cert5.C099.Base

namespace ReflectZphi.Data.Cert5.C099

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd7_4 : ldCheck G d7_4.U d7_4.ms ldd7_4 = true := by decide +kernel
theorem pre_okd7_4 : subPre G cell7 d7_4 = true := by decide +kernel
theorem subd7_4_0 : subd7_4 [-3] = true := by decide +kernel
theorem subd7_4_1 : subd7_4 [-2] = true := by decide +kernel
theorem subd7_4_2 : subd7_4 [-1, -3] = true := by decide +kernel
theorem subd7_4_3 : subd7_4 [-1, -2] = true := by decide +kernel
theorem subd7_4_4 : subd7_4 [-1, -1] = true := by decide +kernel
theorem subd7_4_5 : subd7_4 [-1, 0] = true := by decide +kernel
theorem subd7_4_6 : subd7_4 [-1, 1] = true := by decide +kernel
theorem subd7_4_7 : subd7_4 [-1, 2] = true := by decide +kernel
theorem subd7_4_8 : subd7_4 [0, -3] = true := by decide +kernel
theorem subd7_4_9 : subd7_4 [0, -2] = true := by decide +kernel
theorem subd7_4_10 : subd7_4 [0, -1] = true := by decide +kernel
theorem subd7_4_11 : subd7_4 [0, 0] = true := by decide +kernel
theorem subd7_4_12 : subd7_4 [0, 1] = true := by decide +kernel
theorem subd7_4_13 : subd7_4 [0, 2] = true := by decide +kernel
theorem subd7_4_14 : subd7_4 [1, -3] = true := by decide +kernel
theorem subd7_4_15 : subd7_4 [1, -2] = true := by decide +kernel
theorem subd7_4_16 : subd7_4 [1, -1] = true := by decide +kernel
theorem subd7_4_17 : subd7_4 [1, 0] = true := by decide +kernel
theorem subd7_4_18 : subd7_4 [1, 1] = true := by decide +kernel
theorem subd7_4_19 : subd7_4 [1, 2] = true := by decide +kernel
theorem subd7_4_20 : subd7_4 [2] = true := by decide +kernel
theorem subd7_4_21 : subd7_4 [3] = true := by decide +kernel
theorem sbd7_4_0 : ∀ q ∈ blkd7_4_0, subd7_4 q = true := by
  unfold blkd7_4_0
  exact List.forall_mem_cons.2 ⟨subd7_4_0, List.forall_mem_cons.2 ⟨subd7_4_1, List.forall_mem_cons.2 ⟨subd7_4_2, List.forall_mem_cons.2 ⟨subd7_4_3, List.forall_mem_cons.2 ⟨subd7_4_4, List.forall_mem_cons.2 ⟨subd7_4_5, List.forall_mem_cons.2 ⟨subd7_4_6, List.forall_mem_cons.2 ⟨subd7_4_7, List.forall_mem_cons.2 ⟨subd7_4_8, List.forall_mem_cons.2 ⟨subd7_4_9, List.forall_mem_cons.2 ⟨subd7_4_10, List.forall_mem_cons.2 ⟨subd7_4_11, List.forall_mem_cons.2 ⟨subd7_4_12, List.forall_mem_cons.2 ⟨subd7_4_13, List.forall_mem_cons.2 ⟨subd7_4_14, List.forall_mem_cons.2 ⟨subd7_4_15, List.forall_mem_cons.2 ⟨subd7_4_16, List.forall_mem_cons.2 ⟨subd7_4_17, List.forall_mem_cons.2 ⟨subd7_4_18, List.forall_mem_cons.2 ⟨subd7_4_19, List.forall_mem_cons.2 ⟨subd7_4_20, List.forall_mem_cons.2 ⟨subd7_4_21, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_5 : ldCheck G d7_5.U d7_5.ms ldd7_5 = true := by decide +kernel
theorem pre_okd7_5 : subPre G cell7 d7_5 = true := by decide +kernel
theorem subd7_5_0 : subd7_5 [-3] = true := by decide +kernel
theorem subd7_5_1 : subd7_5 [-2, -3] = true := by decide +kernel
theorem subd7_5_2 : subd7_5 [-2, -2] = true := by decide +kernel
theorem subd7_5_3 : subd7_5 [-2, -1] = true := by decide +kernel
theorem subd7_5_4 : subd7_5 [-2, 0] = true := by decide +kernel
theorem subd7_5_5 : subd7_5 [-2, 1] = true := by decide +kernel
theorem subd7_5_6 : subd7_5 [-2, 2] = true := by decide +kernel
theorem subd7_5_7 : subd7_5 [-2, 3] = true := by decide +kernel
theorem subd7_5_8 : subd7_5 [-1, -4] = true := by decide +kernel
theorem subd7_5_9 : subd7_5 [-1, -3] = true := by decide +kernel
theorem subd7_5_10 : subd7_5 [-1, -2] = true := by decide +kernel
theorem subd7_5_11 : subd7_5 [-1, -1] = true := by decide +kernel
theorem subd7_5_12 : subd7_5 [-1, 0] = true := by decide +kernel
theorem subd7_5_13 : subd7_5 [-1, 1] = true := by decide +kernel
theorem subd7_5_14 : subd7_5 [-1, 2] = true := by decide +kernel
theorem subd7_5_15 : subd7_5 [-1, 3] = true := by decide +kernel
theorem subd7_5_16 : subd7_5 [0, -4] = true := by decide +kernel
theorem subd7_5_17 : subd7_5 [0, -3] = true := by decide +kernel
theorem subd7_5_18 : subd7_5 [0, -2] = true := by decide +kernel
theorem subd7_5_19 : subd7_5 [0, -1] = true := by decide +kernel
theorem subd7_5_20 : subd7_5 [0, 0] = true := by decide +kernel
theorem subd7_5_21 : subd7_5 [0, 1] = true := by decide +kernel
theorem subd7_5_22 : subd7_5 [0, 2] = true := by decide +kernel
theorem subd7_5_23 : subd7_5 [0, 3] = true := by decide +kernel
theorem subd7_5_24 : subd7_5 [1, -4] = true := by decide +kernel
theorem subd7_5_25 : subd7_5 [1, -3] = true := by decide +kernel
theorem subd7_5_26 : subd7_5 [1, -2] = true := by decide +kernel
theorem subd7_5_27 : subd7_5 [1, -1] = true := by decide +kernel
theorem subd7_5_28 : subd7_5 [1, 0] = true := by decide +kernel
theorem subd7_5_29 : subd7_5 [1, 1] = true := by decide +kernel
theorem subd7_5_30 : subd7_5 [1, 2] = true := by decide +kernel
theorem subd7_5_31 : subd7_5 [1, 3] = true := by decide +kernel
theorem sbd7_5_0 : ∀ q ∈ blkd7_5_0, subd7_5 q = true := by
  unfold blkd7_5_0
  exact List.forall_mem_cons.2 ⟨subd7_5_0, List.forall_mem_cons.2 ⟨subd7_5_1, List.forall_mem_cons.2 ⟨subd7_5_2, List.forall_mem_cons.2 ⟨subd7_5_3, List.forall_mem_cons.2 ⟨subd7_5_4, List.forall_mem_cons.2 ⟨subd7_5_5, List.forall_mem_cons.2 ⟨subd7_5_6, List.forall_mem_cons.2 ⟨subd7_5_7, List.forall_mem_cons.2 ⟨subd7_5_8, List.forall_mem_cons.2 ⟨subd7_5_9, List.forall_mem_cons.2 ⟨subd7_5_10, List.forall_mem_cons.2 ⟨subd7_5_11, List.forall_mem_cons.2 ⟨subd7_5_12, List.forall_mem_cons.2 ⟨subd7_5_13, List.forall_mem_cons.2 ⟨subd7_5_14, List.forall_mem_cons.2 ⟨subd7_5_15, List.forall_mem_cons.2 ⟨subd7_5_16, List.forall_mem_cons.2 ⟨subd7_5_17, List.forall_mem_cons.2 ⟨subd7_5_18, List.forall_mem_cons.2 ⟨subd7_5_19, List.forall_mem_cons.2 ⟨subd7_5_20, List.forall_mem_cons.2 ⟨subd7_5_21, List.forall_mem_cons.2 ⟨subd7_5_22, List.forall_mem_cons.2 ⟨subd7_5_23, List.forall_mem_cons.2 ⟨subd7_5_24, List.forall_mem_cons.2 ⟨subd7_5_25, List.forall_mem_cons.2 ⟨subd7_5_26, List.forall_mem_cons.2 ⟨subd7_5_27, List.forall_mem_cons.2 ⟨subd7_5_28, List.forall_mem_cons.2 ⟨subd7_5_29, List.forall_mem_cons.2 ⟨subd7_5_30, List.forall_mem_cons.2 ⟨subd7_5_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_5_32 : subd7_5 [2, -4] = true := by decide +kernel
theorem subd7_5_33 : subd7_5 [2, -3] = true := by decide +kernel
theorem subd7_5_34 : subd7_5 [2, -2] = true := by decide +kernel
theorem subd7_5_35 : subd7_5 [2, -1] = true := by decide +kernel
theorem subd7_5_36 : subd7_5 [2, 0] = true := by decide +kernel
theorem subd7_5_37 : subd7_5 [2, 1] = true := by decide +kernel
theorem subd7_5_38 : subd7_5 [2, 2] = true := by decide +kernel
theorem subd7_5_39 : subd7_5 [3] = true := by decide +kernel
theorem sbd7_5_1 : ∀ q ∈ blkd7_5_1, subd7_5 q = true := by
  unfold blkd7_5_1
  exact List.forall_mem_cons.2 ⟨subd7_5_32, List.forall_mem_cons.2 ⟨subd7_5_33, List.forall_mem_cons.2 ⟨subd7_5_34, List.forall_mem_cons.2 ⟨subd7_5_35, List.forall_mem_cons.2 ⟨subd7_5_36, List.forall_mem_cons.2 ⟨subd7_5_37, List.forall_mem_cons.2 ⟨subd7_5_38, List.forall_mem_cons.2 ⟨subd7_5_39, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
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
theorem subd7_6_8 : subd7_6 [-3, -4] = true := by decide +kernel
theorem subd7_6_9 : subd7_6 [-3, -3] = true := by decide +kernel
theorem subd7_6_10 : subd7_6 [-3, -2] = true := by decide +kernel
theorem subd7_6_11 : subd7_6 [-3, -1] = true := by decide +kernel
theorem subd7_6_12 : subd7_6 [-3, 0] = true := by decide +kernel
theorem subd7_6_13 : subd7_6 [-3, 1] = true := by decide +kernel
theorem subd7_6_14 : subd7_6 [-3, 2] = true := by decide +kernel
theorem subd7_6_15 : subd7_6 [-3, 3] = true := by decide +kernel
theorem subd7_6_16 : subd7_6 [-3, 4] = true := by decide +kernel
theorem subd7_6_17 : subd7_6 [-2, -5] = true := by decide +kernel
theorem subd7_6_18 : subd7_6 [-2, -4] = true := by decide +kernel
theorem subd7_6_19 : subd7_6 [-2, -3] = true := by decide +kernel
theorem subd7_6_20 : subd7_6 [-2, -2] = true := by decide +kernel
theorem subd7_6_21 : subd7_6 [-2, -1] = true := by decide +kernel
theorem subd7_6_22 : subd7_6 [-2, 0] = true := by decide +kernel
theorem subd7_6_23 : subd7_6 [-2, 1] = true := by decide +kernel
theorem subd7_6_24 : subd7_6 [-2, 2] = true := by decide +kernel
theorem subd7_6_25 : subd7_6 [-2, 3] = true := by decide +kernel
theorem subd7_6_26 : subd7_6 [-2, 4] = true := by decide +kernel
theorem subd7_6_27 : subd7_6 [-1, -5] = true := by decide +kernel
theorem subd7_6_28 : subd7_6 [-1, -4] = true := by decide +kernel
theorem subd7_6_29 : subd7_6 [-1, -3] = true := by decide +kernel
theorem subd7_6_30 : subd7_6 [-1, -2] = true := by decide +kernel
theorem subd7_6_31 : subd7_6 [-1, -1] = true := by decide +kernel
theorem sbd7_6_0 : ∀ q ∈ blkd7_6_0, subd7_6 q = true := by
  unfold blkd7_6_0
  exact List.forall_mem_cons.2 ⟨subd7_6_0, List.forall_mem_cons.2 ⟨subd7_6_1, List.forall_mem_cons.2 ⟨subd7_6_2, List.forall_mem_cons.2 ⟨subd7_6_3, List.forall_mem_cons.2 ⟨subd7_6_4, List.forall_mem_cons.2 ⟨subd7_6_5, List.forall_mem_cons.2 ⟨subd7_6_6, List.forall_mem_cons.2 ⟨subd7_6_7, List.forall_mem_cons.2 ⟨subd7_6_8, List.forall_mem_cons.2 ⟨subd7_6_9, List.forall_mem_cons.2 ⟨subd7_6_10, List.forall_mem_cons.2 ⟨subd7_6_11, List.forall_mem_cons.2 ⟨subd7_6_12, List.forall_mem_cons.2 ⟨subd7_6_13, List.forall_mem_cons.2 ⟨subd7_6_14, List.forall_mem_cons.2 ⟨subd7_6_15, List.forall_mem_cons.2 ⟨subd7_6_16, List.forall_mem_cons.2 ⟨subd7_6_17, List.forall_mem_cons.2 ⟨subd7_6_18, List.forall_mem_cons.2 ⟨subd7_6_19, List.forall_mem_cons.2 ⟨subd7_6_20, List.forall_mem_cons.2 ⟨subd7_6_21, List.forall_mem_cons.2 ⟨subd7_6_22, List.forall_mem_cons.2 ⟨subd7_6_23, List.forall_mem_cons.2 ⟨subd7_6_24, List.forall_mem_cons.2 ⟨subd7_6_25, List.forall_mem_cons.2 ⟨subd7_6_26, List.forall_mem_cons.2 ⟨subd7_6_27, List.forall_mem_cons.2 ⟨subd7_6_28, List.forall_mem_cons.2 ⟨subd7_6_29, List.forall_mem_cons.2 ⟨subd7_6_30, List.forall_mem_cons.2 ⟨subd7_6_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C099
