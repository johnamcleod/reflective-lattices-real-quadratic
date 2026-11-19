import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd25_3_0 : subd25_3 [-3] = true := by decide +kernel
theorem subd25_3_1 : subd25_3 [-2] = true := by decide +kernel
theorem subd25_3_2 : subd25_3 [-1, -4] = true := by decide +kernel
theorem subd25_3_3 : subd25_3 [-1, -3] = true := by decide +kernel
theorem subd25_3_4 : subd25_3 [-1, -2] = true := by decide +kernel
theorem subd25_3_5 : subd25_3 [-1, -1] = true := by decide +kernel
theorem subd25_3_6 : subd25_3 [-1, 0] = true := by decide +kernel
theorem subd25_3_7 : subd25_3 [-1, 1] = true := by decide +kernel
theorem subd25_3_8 : subd25_3 [-1, 2] = true := by decide +kernel
theorem subd25_3_9 : subd25_3 [0, -4] = true := by decide +kernel
theorem subd25_3_10 : subd25_3 [0, -3] = true := by decide +kernel
theorem subd25_3_11 : subd25_3 [0, -2] = true := by decide +kernel
theorem subd25_3_12 : subd25_3 [0, -1] = true := by decide +kernel
theorem subd25_3_13 : subd25_3 [0, 0] = true := by decide +kernel
theorem subd25_3_14 : subd25_3 [0, 1] = true := by decide +kernel
theorem subd25_3_15 : subd25_3 [0, 2] = true := by decide +kernel
theorem subd25_3_16 : subd25_3 [0, 3] = true := by decide +kernel
theorem subd25_3_17 : subd25_3 [1, -3] = true := by decide +kernel
theorem subd25_3_18 : subd25_3 [1, -2] = true := by decide +kernel
theorem subd25_3_19 : subd25_3 [1, -1] = true := by decide +kernel
theorem subd25_3_20 : subd25_3 [1, 0] = true := by decide +kernel
theorem subd25_3_21 : subd25_3 [1, 1] = true := by decide +kernel
theorem subd25_3_22 : subd25_3 [1, 2] = true := by decide +kernel
theorem subd25_3_23 : subd25_3 [1, 3] = true := by decide +kernel
theorem subd25_3_24 : subd25_3 [2] = true := by decide +kernel
theorem subd25_3_25 : subd25_3 [3] = true := by decide +kernel
theorem sbd25_3_0 : ∀ q ∈ blkd25_3_0, subd25_3 q = true := by
  unfold blkd25_3_0
  exact List.forall_mem_cons.2 ⟨subd25_3_0, List.forall_mem_cons.2 ⟨subd25_3_1, List.forall_mem_cons.2 ⟨subd25_3_2, List.forall_mem_cons.2 ⟨subd25_3_3, List.forall_mem_cons.2 ⟨subd25_3_4, List.forall_mem_cons.2 ⟨subd25_3_5, List.forall_mem_cons.2 ⟨subd25_3_6, List.forall_mem_cons.2 ⟨subd25_3_7, List.forall_mem_cons.2 ⟨subd25_3_8, List.forall_mem_cons.2 ⟨subd25_3_9, List.forall_mem_cons.2 ⟨subd25_3_10, List.forall_mem_cons.2 ⟨subd25_3_11, List.forall_mem_cons.2 ⟨subd25_3_12, List.forall_mem_cons.2 ⟨subd25_3_13, List.forall_mem_cons.2 ⟨subd25_3_14, List.forall_mem_cons.2 ⟨subd25_3_15, List.forall_mem_cons.2 ⟨subd25_3_16, List.forall_mem_cons.2 ⟨subd25_3_17, List.forall_mem_cons.2 ⟨subd25_3_18, List.forall_mem_cons.2 ⟨subd25_3_19, List.forall_mem_cons.2 ⟨subd25_3_20, List.forall_mem_cons.2 ⟨subd25_3_21, List.forall_mem_cons.2 ⟨subd25_3_22, List.forall_mem_cons.2 ⟨subd25_3_23, List.forall_mem_cons.2 ⟨subd25_3_24, List.forall_mem_cons.2 ⟨subd25_3_25, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd26_0 : ldCheck G d26_0.U d26_0.ms ldd26_0 = true := by decide +kernel
theorem pre_okd26_0 : subPre G cell26 d26_0 = true := by decide +kernel
theorem subd26_0_0 : subd26_0 [-2] = true := by decide +kernel
theorem subd26_0_1 : subd26_0 [-1, -3] = true := by decide +kernel
theorem subd26_0_2 : subd26_0 [-1, -2] = true := by decide +kernel
theorem subd26_0_3 : subd26_0 [-1, -1] = true := by decide +kernel
theorem subd26_0_4 : subd26_0 [-1, 0] = true := by decide +kernel
theorem subd26_0_5 : subd26_0 [-1, 1] = true := by decide +kernel
theorem subd26_0_6 : subd26_0 [-1, 2] = true := by decide +kernel
theorem subd26_0_7 : subd26_0 [0, -3] = true := by decide +kernel
theorem subd26_0_8 : subd26_0 [0, -2] = true := by decide +kernel
theorem subd26_0_9 : subd26_0 [0, -1] = true := by decide +kernel
theorem subd26_0_10 : subd26_0 [0, 0] = true := by decide +kernel
theorem subd26_0_11 : subd26_0 [0, 1] = true := by decide +kernel
theorem subd26_0_12 : subd26_0 [0, 2] = true := by decide +kernel
theorem subd26_0_13 : subd26_0 [1, -3] = true := by decide +kernel
theorem subd26_0_14 : subd26_0 [1, -2] = true := by decide +kernel
theorem subd26_0_15 : subd26_0 [1, -1] = true := by decide +kernel
theorem subd26_0_16 : subd26_0 [1, 0] = true := by decide +kernel
theorem subd26_0_17 : subd26_0 [1, 1] = true := by decide +kernel
theorem subd26_0_18 : subd26_0 [1, 2] = true := by decide +kernel
theorem subd26_0_19 : subd26_0 [2] = true := by decide +kernel
theorem sbd26_0_0 : ∀ q ∈ blkd26_0_0, subd26_0 q = true := by
  unfold blkd26_0_0
  exact List.forall_mem_cons.2 ⟨subd26_0_0, List.forall_mem_cons.2 ⟨subd26_0_1, List.forall_mem_cons.2 ⟨subd26_0_2, List.forall_mem_cons.2 ⟨subd26_0_3, List.forall_mem_cons.2 ⟨subd26_0_4, List.forall_mem_cons.2 ⟨subd26_0_5, List.forall_mem_cons.2 ⟨subd26_0_6, List.forall_mem_cons.2 ⟨subd26_0_7, List.forall_mem_cons.2 ⟨subd26_0_8, List.forall_mem_cons.2 ⟨subd26_0_9, List.forall_mem_cons.2 ⟨subd26_0_10, List.forall_mem_cons.2 ⟨subd26_0_11, List.forall_mem_cons.2 ⟨subd26_0_12, List.forall_mem_cons.2 ⟨subd26_0_13, List.forall_mem_cons.2 ⟨subd26_0_14, List.forall_mem_cons.2 ⟨subd26_0_15, List.forall_mem_cons.2 ⟨subd26_0_16, List.forall_mem_cons.2 ⟨subd26_0_17, List.forall_mem_cons.2 ⟨subd26_0_18, List.forall_mem_cons.2 ⟨subd26_0_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd26_1 : ldCheck G d26_1.U d26_1.ms ldd26_1 = true := by decide +kernel
theorem pre_okd26_1 : subPre G cell26 d26_1 = true := by decide +kernel
theorem subd26_1_0 : subd26_1 [-3] = true := by decide +kernel
theorem subd26_1_1 : subd26_1 [-2, -3] = true := by decide +kernel
theorem subd26_1_2 : subd26_1 [-2, -2] = true := by decide +kernel
theorem subd26_1_3 : subd26_1 [-2, -1] = true := by decide +kernel
theorem subd26_1_4 : subd26_1 [-2, 0] = true := by decide +kernel
theorem subd26_1_5 : subd26_1 [-2, 1] = true := by decide +kernel
theorem subd26_1_6 : subd26_1 [-2, 2] = true := by decide +kernel
theorem subd26_1_7 : subd26_1 [-2, 3] = true := by decide +kernel
theorem subd26_1_8 : subd26_1 [-1, -4] = true := by decide +kernel
theorem subd26_1_9 : subd26_1 [-1, -3] = true := by decide +kernel
theorem subd26_1_10 : subd26_1 [-1, -2] = true := by decide +kernel
theorem subd26_1_11 : subd26_1 [-1, -1] = true := by decide +kernel
theorem subd26_1_12 : subd26_1 [-1, 0] = true := by decide +kernel
theorem subd26_1_13 : subd26_1 [-1, 1] = true := by decide +kernel
theorem subd26_1_14 : subd26_1 [-1, 2] = true := by decide +kernel
theorem subd26_1_15 : subd26_1 [-1, 3] = true := by decide +kernel
theorem subd26_1_16 : subd26_1 [-1, 4] = true := by decide +kernel
theorem subd26_1_17 : subd26_1 [0, -4] = true := by decide +kernel
theorem subd26_1_18 : subd26_1 [0, -3] = true := by decide +kernel
theorem subd26_1_19 : subd26_1 [0, -2] = true := by decide +kernel
theorem subd26_1_20 : subd26_1 [0, -1] = true := by decide +kernel
theorem subd26_1_21 : subd26_1 [0, 0] = true := by decide +kernel
theorem subd26_1_22 : subd26_1 [0, 1] = true := by decide +kernel
theorem subd26_1_23 : subd26_1 [0, 2] = true := by decide +kernel
theorem subd26_1_24 : subd26_1 [0, 3] = true := by decide +kernel
theorem subd26_1_25 : subd26_1 [1, -5] = true := by decide +kernel
theorem subd26_1_26 : subd26_1 [1, -4] = true := by decide +kernel
theorem subd26_1_27 : subd26_1 [1, -3] = true := by decide +kernel
theorem subd26_1_28 : subd26_1 [1, -2] = true := by decide +kernel
theorem subd26_1_29 : subd26_1 [1, -1] = true := by decide +kernel
theorem subd26_1_30 : subd26_1 [1, 0] = true := by decide +kernel
theorem subd26_1_31 : subd26_1 [1, 1] = true := by decide +kernel
theorem sbd26_1_0 : ∀ q ∈ blkd26_1_0, subd26_1 q = true := by
  unfold blkd26_1_0
  exact List.forall_mem_cons.2 ⟨subd26_1_0, List.forall_mem_cons.2 ⟨subd26_1_1, List.forall_mem_cons.2 ⟨subd26_1_2, List.forall_mem_cons.2 ⟨subd26_1_3, List.forall_mem_cons.2 ⟨subd26_1_4, List.forall_mem_cons.2 ⟨subd26_1_5, List.forall_mem_cons.2 ⟨subd26_1_6, List.forall_mem_cons.2 ⟨subd26_1_7, List.forall_mem_cons.2 ⟨subd26_1_8, List.forall_mem_cons.2 ⟨subd26_1_9, List.forall_mem_cons.2 ⟨subd26_1_10, List.forall_mem_cons.2 ⟨subd26_1_11, List.forall_mem_cons.2 ⟨subd26_1_12, List.forall_mem_cons.2 ⟨subd26_1_13, List.forall_mem_cons.2 ⟨subd26_1_14, List.forall_mem_cons.2 ⟨subd26_1_15, List.forall_mem_cons.2 ⟨subd26_1_16, List.forall_mem_cons.2 ⟨subd26_1_17, List.forall_mem_cons.2 ⟨subd26_1_18, List.forall_mem_cons.2 ⟨subd26_1_19, List.forall_mem_cons.2 ⟨subd26_1_20, List.forall_mem_cons.2 ⟨subd26_1_21, List.forall_mem_cons.2 ⟨subd26_1_22, List.forall_mem_cons.2 ⟨subd26_1_23, List.forall_mem_cons.2 ⟨subd26_1_24, List.forall_mem_cons.2 ⟨subd26_1_25, List.forall_mem_cons.2 ⟨subd26_1_26, List.forall_mem_cons.2 ⟨subd26_1_27, List.forall_mem_cons.2 ⟨subd26_1_28, List.forall_mem_cons.2 ⟨subd26_1_29, List.forall_mem_cons.2 ⟨subd26_1_30, List.forall_mem_cons.2 ⟨subd26_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd26_1_32 : subd26_1 [1, 2] = true := by decide +kernel
theorem subd26_1_33 : subd26_1 [1, 3] = true := by decide +kernel
theorem subd26_1_34 : subd26_1 [2, -4] = true := by decide +kernel
theorem subd26_1_35 : subd26_1 [2, -3] = true := by decide +kernel
theorem subd26_1_36 : subd26_1 [2, -2] = true := by decide +kernel
theorem subd26_1_37 : subd26_1 [2, -1] = true := by decide +kernel
theorem subd26_1_38 : subd26_1 [2, 0] = true := by decide +kernel
theorem subd26_1_39 : subd26_1 [2, 1] = true := by decide +kernel
theorem subd26_1_40 : subd26_1 [2, 2] = true := by decide +kernel
theorem subd26_1_41 : subd26_1 [3] = true := by decide +kernel
theorem sbd26_1_1 : ∀ q ∈ blkd26_1_1, subd26_1 q = true := by
  unfold blkd26_1_1
  exact List.forall_mem_cons.2 ⟨subd26_1_32, List.forall_mem_cons.2 ⟨subd26_1_33, List.forall_mem_cons.2 ⟨subd26_1_34, List.forall_mem_cons.2 ⟨subd26_1_35, List.forall_mem_cons.2 ⟨subd26_1_36, List.forall_mem_cons.2 ⟨subd26_1_37, List.forall_mem_cons.2 ⟨subd26_1_38, List.forall_mem_cons.2 ⟨subd26_1_39, List.forall_mem_cons.2 ⟨subd26_1_40, List.forall_mem_cons.2 ⟨subd26_1_41, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd26_2 : ldCheck G d26_2.U d26_2.ms ldd26_2 = true := by decide +kernel
theorem pre_okd26_2 : subPre G cell26 d26_2 = true := by decide +kernel
theorem subd26_2_0 : subd26_2 [-1, -2] = true := by decide +kernel
theorem subd26_2_1 : subd26_2 [-1, -1] = true := by decide +kernel
theorem subd26_2_2 : subd26_2 [-1, 0] = true := by decide +kernel
theorem subd26_2_3 : subd26_2 [0, -2] = true := by decide +kernel
theorem subd26_2_4 : subd26_2 [0, -1] = true := by decide +kernel
theorem subd26_2_5 : subd26_2 [0, 0, -9] = true := by decide +kernel
theorem subd26_2_6 : subd26_2 [0, 0, -8] = true := by decide +kernel
theorem subd26_2_7 : subd26_2 [0, 0, -7] = true := by decide +kernel
theorem subd26_2_8 : subd26_2 [0, 0, -6] = true := by decide +kernel
theorem subd26_2_9 : subd26_2 [0, 0, -5] = true := by decide +kernel
theorem subd26_2_10 : subd26_2 [0, 0, -4] = true := by decide +kernel
theorem subd26_2_11 : subd26_2 [0, 0, -3] = true := by decide +kernel
theorem subd26_2_12 : subd26_2 [0, 0, -2] = true := by decide +kernel
theorem subd26_2_13 : subd26_2 [0, 0, -1] = true := by decide +kernel
theorem subd26_2_14 : subd26_2 [0, 0, 0] = true := by decide +kernel
theorem subd26_2_15 : subd26_2 [0, 0, 1] = true := by decide +kernel
theorem subd26_2_16 : subd26_2 [0, 0, 2] = true := by decide +kernel
theorem subd26_2_17 : subd26_2 [0, 0, 3] = true := by decide +kernel
theorem subd26_2_18 : subd26_2 [0, 0, 4] = true := by decide +kernel
theorem subd26_2_19 : subd26_2 [0, 0, 5] = true := by decide +kernel
theorem subd26_2_20 : subd26_2 [0, 0, 6] = true := by decide +kernel
theorem subd26_2_21 : subd26_2 [0, 0, 7] = true := by decide +kernel
theorem subd26_2_22 : subd26_2 [0, 0, 8] = true := by decide +kernel
theorem subd26_2_23 : subd26_2 [0, 1] = true := by decide +kernel
theorem subd26_2_24 : subd26_2 [1, -1] = true := by decide +kernel
theorem subd26_2_25 : subd26_2 [1, 0] = true := by decide +kernel
theorem subd26_2_26 : subd26_2 [1, 1] = true := by decide +kernel
theorem sbd26_2_0 : ∀ q ∈ blkd26_2_0, subd26_2 q = true := by
  unfold blkd26_2_0
  exact List.forall_mem_cons.2 ⟨subd26_2_0, List.forall_mem_cons.2 ⟨subd26_2_1, List.forall_mem_cons.2 ⟨subd26_2_2, List.forall_mem_cons.2 ⟨subd26_2_3, List.forall_mem_cons.2 ⟨subd26_2_4, List.forall_mem_cons.2 ⟨subd26_2_5, List.forall_mem_cons.2 ⟨subd26_2_6, List.forall_mem_cons.2 ⟨subd26_2_7, List.forall_mem_cons.2 ⟨subd26_2_8, List.forall_mem_cons.2 ⟨subd26_2_9, List.forall_mem_cons.2 ⟨subd26_2_10, List.forall_mem_cons.2 ⟨subd26_2_11, List.forall_mem_cons.2 ⟨subd26_2_12, List.forall_mem_cons.2 ⟨subd26_2_13, List.forall_mem_cons.2 ⟨subd26_2_14, List.forall_mem_cons.2 ⟨subd26_2_15, List.forall_mem_cons.2 ⟨subd26_2_16, List.forall_mem_cons.2 ⟨subd26_2_17, List.forall_mem_cons.2 ⟨subd26_2_18, List.forall_mem_cons.2 ⟨subd26_2_19, List.forall_mem_cons.2 ⟨subd26_2_20, List.forall_mem_cons.2 ⟨subd26_2_21, List.forall_mem_cons.2 ⟨subd26_2_22, List.forall_mem_cons.2 ⟨subd26_2_23, List.forall_mem_cons.2 ⟨subd26_2_24, List.forall_mem_cons.2 ⟨subd26_2_25, List.forall_mem_cons.2 ⟨subd26_2_26, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd26_3 : ldCheck G d26_3.U d26_3.ms ldd26_3 = true := by decide +kernel
theorem pre_okd26_3 : subPre G cell26 d26_3 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C143
