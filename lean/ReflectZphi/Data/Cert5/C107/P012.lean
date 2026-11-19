import ReflectZphi.Data.Cert5.C107.Base

namespace ReflectZphi.Data.Cert5.C107

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd7_0_0 : subd7_0 [-4] = true := by decide +kernel
theorem subd7_0_1 : subd7_0 [-3] = true := by decide +kernel
theorem subd7_0_2 : subd7_0 [-2, -4] = true := by decide +kernel
theorem subd7_0_3 : subd7_0 [-2, -3] = true := by decide +kernel
theorem subd7_0_4 : subd7_0 [-2, -2] = true := by decide +kernel
theorem subd7_0_5 : subd7_0 [-2, -1] = true := by decide +kernel
theorem subd7_0_6 : subd7_0 [-2, 0] = true := by decide +kernel
theorem subd7_0_7 : subd7_0 [-2, 1] = true := by decide +kernel
theorem subd7_0_8 : subd7_0 [-2, 2] = true := by decide +kernel
theorem subd7_0_9 : subd7_0 [-1, -4] = true := by decide +kernel
theorem subd7_0_10 : subd7_0 [-1, -3] = true := by decide +kernel
theorem subd7_0_11 : subd7_0 [-1, -2] = true := by decide +kernel
theorem subd7_0_12 : subd7_0 [-1, -1] = true := by decide +kernel
theorem subd7_0_13 : subd7_0 [-1, 0] = true := by decide +kernel
theorem subd7_0_14 : subd7_0 [-1, 1] = true := by decide +kernel
theorem subd7_0_15 : subd7_0 [-1, 2] = true := by decide +kernel
theorem subd7_0_16 : subd7_0 [-1, 3] = true := by decide +kernel
theorem subd7_0_17 : subd7_0 [0, -4] = true := by decide +kernel
theorem subd7_0_18 : subd7_0 [0, -3] = true := by decide +kernel
theorem subd7_0_19 : subd7_0 [0, -2] = true := by decide +kernel
theorem subd7_0_20 : subd7_0 [0, -1] = true := by decide +kernel
theorem subd7_0_21 : subd7_0 [0, 0] = true := by decide +kernel
theorem subd7_0_22 : subd7_0 [0, 1] = true := by decide +kernel
theorem subd7_0_23 : subd7_0 [0, 2] = true := by decide +kernel
theorem subd7_0_24 : subd7_0 [0, 3] = true := by decide +kernel
theorem subd7_0_25 : subd7_0 [1, -4] = true := by decide +kernel
theorem subd7_0_26 : subd7_0 [1, -3] = true := by decide +kernel
theorem subd7_0_27 : subd7_0 [1, -2] = true := by decide +kernel
theorem subd7_0_28 : subd7_0 [1, -1] = true := by decide +kernel
theorem subd7_0_29 : subd7_0 [1, 0] = true := by decide +kernel
theorem subd7_0_30 : subd7_0 [1, 1] = true := by decide +kernel
theorem subd7_0_31 : subd7_0 [1, 2] = true := by decide +kernel
theorem sbd7_0_0 : ∀ q ∈ blkd7_0_0, subd7_0 q = true := by
  unfold blkd7_0_0
  exact List.forall_mem_cons.2 ⟨subd7_0_0, List.forall_mem_cons.2 ⟨subd7_0_1, List.forall_mem_cons.2 ⟨subd7_0_2, List.forall_mem_cons.2 ⟨subd7_0_3, List.forall_mem_cons.2 ⟨subd7_0_4, List.forall_mem_cons.2 ⟨subd7_0_5, List.forall_mem_cons.2 ⟨subd7_0_6, List.forall_mem_cons.2 ⟨subd7_0_7, List.forall_mem_cons.2 ⟨subd7_0_8, List.forall_mem_cons.2 ⟨subd7_0_9, List.forall_mem_cons.2 ⟨subd7_0_10, List.forall_mem_cons.2 ⟨subd7_0_11, List.forall_mem_cons.2 ⟨subd7_0_12, List.forall_mem_cons.2 ⟨subd7_0_13, List.forall_mem_cons.2 ⟨subd7_0_14, List.forall_mem_cons.2 ⟨subd7_0_15, List.forall_mem_cons.2 ⟨subd7_0_16, List.forall_mem_cons.2 ⟨subd7_0_17, List.forall_mem_cons.2 ⟨subd7_0_18, List.forall_mem_cons.2 ⟨subd7_0_19, List.forall_mem_cons.2 ⟨subd7_0_20, List.forall_mem_cons.2 ⟨subd7_0_21, List.forall_mem_cons.2 ⟨subd7_0_22, List.forall_mem_cons.2 ⟨subd7_0_23, List.forall_mem_cons.2 ⟨subd7_0_24, List.forall_mem_cons.2 ⟨subd7_0_25, List.forall_mem_cons.2 ⟨subd7_0_26, List.forall_mem_cons.2 ⟨subd7_0_27, List.forall_mem_cons.2 ⟨subd7_0_28, List.forall_mem_cons.2 ⟨subd7_0_29, List.forall_mem_cons.2 ⟨subd7_0_30, List.forall_mem_cons.2 ⟨subd7_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_32 : subd7_0 [1, 3] = true := by decide +kernel
theorem subd7_0_33 : subd7_0 [2, -3] = true := by decide +kernel
theorem subd7_0_34 : subd7_0 [2, -2] = true := by decide +kernel
theorem subd7_0_35 : subd7_0 [2, -1] = true := by decide +kernel
theorem subd7_0_36 : subd7_0 [2, 0] = true := by decide +kernel
theorem subd7_0_37 : subd7_0 [2, 1] = true := by decide +kernel
theorem subd7_0_38 : subd7_0 [2, 2] = true := by decide +kernel
theorem subd7_0_39 : subd7_0 [2, 3] = true := by decide +kernel
theorem subd7_0_40 : subd7_0 [3] = true := by decide +kernel
theorem subd7_0_41 : subd7_0 [4] = true := by decide +kernel
theorem sbd7_0_1 : ∀ q ∈ blkd7_0_1, subd7_0 q = true := by
  unfold blkd7_0_1
  exact List.forall_mem_cons.2 ⟨subd7_0_32, List.forall_mem_cons.2 ⟨subd7_0_33, List.forall_mem_cons.2 ⟨subd7_0_34, List.forall_mem_cons.2 ⟨subd7_0_35, List.forall_mem_cons.2 ⟨subd7_0_36, List.forall_mem_cons.2 ⟨subd7_0_37, List.forall_mem_cons.2 ⟨subd7_0_38, List.forall_mem_cons.2 ⟨subd7_0_39, List.forall_mem_cons.2 ⟨subd7_0_40, List.forall_mem_cons.2 ⟨subd7_0_41, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_1 : ldCheck G d7_1.U d7_1.ms ldd7_1 = true := by decide +kernel
theorem pre_okd7_1 : subPre G cell7 d7_1 = true := by decide +kernel
theorem subd7_1_0 : subd7_1 [-3] = true := by decide +kernel
theorem subd7_1_1 : subd7_1 [-2, -3] = true := by decide +kernel
theorem subd7_1_2 : subd7_1 [-2, -2] = true := by decide +kernel
theorem subd7_1_3 : subd7_1 [-2, -1] = true := by decide +kernel
theorem subd7_1_4 : subd7_1 [-2, 0] = true := by decide +kernel
theorem subd7_1_5 : subd7_1 [-2, 1] = true := by decide +kernel
theorem subd7_1_6 : subd7_1 [-2, 2] = true := by decide +kernel
theorem subd7_1_7 : subd7_1 [-2, 3] = true := by decide +kernel
theorem subd7_1_8 : subd7_1 [-1, -4] = true := by decide +kernel
theorem subd7_1_9 : subd7_1 [-1, -3] = true := by decide +kernel
theorem subd7_1_10 : subd7_1 [-1, -2] = true := by decide +kernel
theorem subd7_1_11 : subd7_1 [-1, -1] = true := by decide +kernel
theorem subd7_1_12 : subd7_1 [-1, 0] = true := by decide +kernel
theorem subd7_1_13 : subd7_1 [-1, 1] = true := by decide +kernel
theorem subd7_1_14 : subd7_1 [-1, 2] = true := by decide +kernel
theorem subd7_1_15 : subd7_1 [-1, 3] = true := by decide +kernel
theorem subd7_1_16 : subd7_1 [0, -4] = true := by decide +kernel
theorem subd7_1_17 : subd7_1 [0, -3] = true := by decide +kernel
theorem subd7_1_18 : subd7_1 [0, -2] = true := by decide +kernel
theorem subd7_1_19 : subd7_1 [0, -1] = true := by decide +kernel
theorem subd7_1_20 : subd7_1 [0, 0] = true := by decide +kernel
theorem subd7_1_21 : subd7_1 [0, 1] = true := by decide +kernel
theorem subd7_1_22 : subd7_1 [0, 2] = true := by decide +kernel
theorem subd7_1_23 : subd7_1 [0, 3] = true := by decide +kernel
theorem subd7_1_24 : subd7_1 [1, -4] = true := by decide +kernel
theorem subd7_1_25 : subd7_1 [1, -3] = true := by decide +kernel
theorem subd7_1_26 : subd7_1 [1, -2] = true := by decide +kernel
theorem subd7_1_27 : subd7_1 [1, -1] = true := by decide +kernel
theorem subd7_1_28 : subd7_1 [1, 0] = true := by decide +kernel
theorem subd7_1_29 : subd7_1 [1, 1] = true := by decide +kernel
theorem subd7_1_30 : subd7_1 [1, 2] = true := by decide +kernel
theorem subd7_1_31 : subd7_1 [1, 3] = true := by decide +kernel
theorem sbd7_1_0 : ∀ q ∈ blkd7_1_0, subd7_1 q = true := by
  unfold blkd7_1_0
  exact List.forall_mem_cons.2 ⟨subd7_1_0, List.forall_mem_cons.2 ⟨subd7_1_1, List.forall_mem_cons.2 ⟨subd7_1_2, List.forall_mem_cons.2 ⟨subd7_1_3, List.forall_mem_cons.2 ⟨subd7_1_4, List.forall_mem_cons.2 ⟨subd7_1_5, List.forall_mem_cons.2 ⟨subd7_1_6, List.forall_mem_cons.2 ⟨subd7_1_7, List.forall_mem_cons.2 ⟨subd7_1_8, List.forall_mem_cons.2 ⟨subd7_1_9, List.forall_mem_cons.2 ⟨subd7_1_10, List.forall_mem_cons.2 ⟨subd7_1_11, List.forall_mem_cons.2 ⟨subd7_1_12, List.forall_mem_cons.2 ⟨subd7_1_13, List.forall_mem_cons.2 ⟨subd7_1_14, List.forall_mem_cons.2 ⟨subd7_1_15, List.forall_mem_cons.2 ⟨subd7_1_16, List.forall_mem_cons.2 ⟨subd7_1_17, List.forall_mem_cons.2 ⟨subd7_1_18, List.forall_mem_cons.2 ⟨subd7_1_19, List.forall_mem_cons.2 ⟨subd7_1_20, List.forall_mem_cons.2 ⟨subd7_1_21, List.forall_mem_cons.2 ⟨subd7_1_22, List.forall_mem_cons.2 ⟨subd7_1_23, List.forall_mem_cons.2 ⟨subd7_1_24, List.forall_mem_cons.2 ⟨subd7_1_25, List.forall_mem_cons.2 ⟨subd7_1_26, List.forall_mem_cons.2 ⟨subd7_1_27, List.forall_mem_cons.2 ⟨subd7_1_28, List.forall_mem_cons.2 ⟨subd7_1_29, List.forall_mem_cons.2 ⟨subd7_1_30, List.forall_mem_cons.2 ⟨subd7_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_32 : subd7_1 [2, -4] = true := by decide +kernel
theorem subd7_1_33 : subd7_1 [2, -3] = true := by decide +kernel
theorem subd7_1_34 : subd7_1 [2, -2] = true := by decide +kernel
theorem subd7_1_35 : subd7_1 [2, -1] = true := by decide +kernel
theorem subd7_1_36 : subd7_1 [2, 0] = true := by decide +kernel
theorem subd7_1_37 : subd7_1 [2, 1] = true := by decide +kernel
theorem subd7_1_38 : subd7_1 [2, 2] = true := by decide +kernel
theorem subd7_1_39 : subd7_1 [3] = true := by decide +kernel
theorem sbd7_1_1 : ∀ q ∈ blkd7_1_1, subd7_1 q = true := by
  unfold blkd7_1_1
  exact List.forall_mem_cons.2 ⟨subd7_1_32, List.forall_mem_cons.2 ⟨subd7_1_33, List.forall_mem_cons.2 ⟨subd7_1_34, List.forall_mem_cons.2 ⟨subd7_1_35, List.forall_mem_cons.2 ⟨subd7_1_36, List.forall_mem_cons.2 ⟨subd7_1_37, List.forall_mem_cons.2 ⟨subd7_1_38, List.forall_mem_cons.2 ⟨subd7_1_39, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_2 : ldCheck G d7_2.U d7_2.ms ldd7_2 = true := by decide +kernel
theorem pre_okd7_2 : subPre G cell7 d7_2 = true := by decide +kernel
theorem subd7_2_0 : subd7_2 [-4] = true := by decide +kernel
theorem subd7_2_1 : subd7_2 [-3] = true := by decide +kernel
theorem subd7_2_2 : subd7_2 [-2, -5] = true := by decide +kernel
theorem subd7_2_3 : subd7_2 [-2, -4] = true := by decide +kernel
theorem subd7_2_4 : subd7_2 [-2, -3] = true := by decide +kernel
theorem subd7_2_5 : subd7_2 [-2, -2] = true := by decide +kernel
theorem subd7_2_6 : subd7_2 [-2, -1] = true := by decide +kernel
theorem subd7_2_7 : subd7_2 [-2, 0] = true := by decide +kernel
theorem subd7_2_8 : subd7_2 [-2, 1] = true := by decide +kernel
theorem subd7_2_9 : subd7_2 [-2, 2] = true := by decide +kernel
theorem subd7_2_10 : subd7_2 [-2, 3] = true := by decide +kernel
theorem subd7_2_11 : subd7_2 [-1, -5] = true := by decide +kernel
theorem subd7_2_12 : subd7_2 [-1, -4] = true := by decide +kernel
theorem subd7_2_13 : subd7_2 [-1, -3] = true := by decide +kernel
theorem subd7_2_14 : subd7_2 [-1, -2] = true := by decide +kernel
theorem subd7_2_15 : subd7_2 [-1, -1] = true := by decide +kernel
theorem subd7_2_16 : subd7_2 [-1, 0] = true := by decide +kernel
theorem subd7_2_17 : subd7_2 [-1, 1] = true := by decide +kernel
theorem subd7_2_18 : subd7_2 [-1, 2] = true := by decide +kernel
theorem subd7_2_19 : subd7_2 [-1, 3] = true := by decide +kernel
theorem subd7_2_20 : subd7_2 [-1, 4] = true := by decide +kernel
theorem subd7_2_21 : subd7_2 [0, -5] = true := by decide +kernel
theorem subd7_2_22 : subd7_2 [0, -4] = true := by decide +kernel
theorem subd7_2_23 : subd7_2 [0, -3] = true := by decide +kernel
theorem subd7_2_24 : subd7_2 [0, -2] = true := by decide +kernel
theorem subd7_2_25 : subd7_2 [0, -1] = true := by decide +kernel
theorem subd7_2_26 : subd7_2 [0, 0] = true := by decide +kernel
theorem subd7_2_27 : subd7_2 [0, 1] = true := by decide +kernel
theorem subd7_2_28 : subd7_2 [0, 2] = true := by decide +kernel
theorem subd7_2_29 : subd7_2 [0, 3] = true := by decide +kernel
theorem subd7_2_30 : subd7_2 [0, 4] = true := by decide +kernel
theorem subd7_2_31 : subd7_2 [1, -5] = true := by decide +kernel
theorem sbd7_2_0 : ∀ q ∈ blkd7_2_0, subd7_2 q = true := by
  unfold blkd7_2_0
  exact List.forall_mem_cons.2 ⟨subd7_2_0, List.forall_mem_cons.2 ⟨subd7_2_1, List.forall_mem_cons.2 ⟨subd7_2_2, List.forall_mem_cons.2 ⟨subd7_2_3, List.forall_mem_cons.2 ⟨subd7_2_4, List.forall_mem_cons.2 ⟨subd7_2_5, List.forall_mem_cons.2 ⟨subd7_2_6, List.forall_mem_cons.2 ⟨subd7_2_7, List.forall_mem_cons.2 ⟨subd7_2_8, List.forall_mem_cons.2 ⟨subd7_2_9, List.forall_mem_cons.2 ⟨subd7_2_10, List.forall_mem_cons.2 ⟨subd7_2_11, List.forall_mem_cons.2 ⟨subd7_2_12, List.forall_mem_cons.2 ⟨subd7_2_13, List.forall_mem_cons.2 ⟨subd7_2_14, List.forall_mem_cons.2 ⟨subd7_2_15, List.forall_mem_cons.2 ⟨subd7_2_16, List.forall_mem_cons.2 ⟨subd7_2_17, List.forall_mem_cons.2 ⟨subd7_2_18, List.forall_mem_cons.2 ⟨subd7_2_19, List.forall_mem_cons.2 ⟨subd7_2_20, List.forall_mem_cons.2 ⟨subd7_2_21, List.forall_mem_cons.2 ⟨subd7_2_22, List.forall_mem_cons.2 ⟨subd7_2_23, List.forall_mem_cons.2 ⟨subd7_2_24, List.forall_mem_cons.2 ⟨subd7_2_25, List.forall_mem_cons.2 ⟨subd7_2_26, List.forall_mem_cons.2 ⟨subd7_2_27, List.forall_mem_cons.2 ⟨subd7_2_28, List.forall_mem_cons.2 ⟨subd7_2_29, List.forall_mem_cons.2 ⟨subd7_2_30, List.forall_mem_cons.2 ⟨subd7_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_32 : subd7_2 [1, -4] = true := by decide +kernel
theorem subd7_2_33 : subd7_2 [1, -3] = true := by decide +kernel
theorem subd7_2_34 : subd7_2 [1, -2] = true := by decide +kernel
theorem subd7_2_35 : subd7_2 [1, -1] = true := by decide +kernel
theorem subd7_2_36 : subd7_2 [1, 0] = true := by decide +kernel
theorem subd7_2_37 : subd7_2 [1, 1] = true := by decide +kernel
theorem subd7_2_38 : subd7_2 [1, 2] = true := by decide +kernel
theorem subd7_2_39 : subd7_2 [1, 3] = true := by decide +kernel
theorem subd7_2_40 : subd7_2 [1, 4] = true := by decide +kernel
theorem subd7_2_41 : subd7_2 [2, -4] = true := by decide +kernel
theorem subd7_2_42 : subd7_2 [2, -3] = true := by decide +kernel
theorem subd7_2_43 : subd7_2 [2, -2] = true := by decide +kernel
theorem subd7_2_44 : subd7_2 [2, -1] = true := by decide +kernel
theorem subd7_2_45 : subd7_2 [2, 0] = true := by decide +kernel
theorem subd7_2_46 : subd7_2 [2, 1] = true := by decide +kernel
theorem subd7_2_47 : subd7_2 [2, 2] = true := by decide +kernel
theorem subd7_2_48 : subd7_2 [2, 3] = true := by decide +kernel
theorem subd7_2_49 : subd7_2 [2, 4] = true := by decide +kernel
theorem subd7_2_50 : subd7_2 [3] = true := by decide +kernel
theorem subd7_2_51 : subd7_2 [4] = true := by decide +kernel
theorem sbd7_2_1 : ∀ q ∈ blkd7_2_1, subd7_2 q = true := by
  unfold blkd7_2_1
  exact List.forall_mem_cons.2 ⟨subd7_2_32, List.forall_mem_cons.2 ⟨subd7_2_33, List.forall_mem_cons.2 ⟨subd7_2_34, List.forall_mem_cons.2 ⟨subd7_2_35, List.forall_mem_cons.2 ⟨subd7_2_36, List.forall_mem_cons.2 ⟨subd7_2_37, List.forall_mem_cons.2 ⟨subd7_2_38, List.forall_mem_cons.2 ⟨subd7_2_39, List.forall_mem_cons.2 ⟨subd7_2_40, List.forall_mem_cons.2 ⟨subd7_2_41, List.forall_mem_cons.2 ⟨subd7_2_42, List.forall_mem_cons.2 ⟨subd7_2_43, List.forall_mem_cons.2 ⟨subd7_2_44, List.forall_mem_cons.2 ⟨subd7_2_45, List.forall_mem_cons.2 ⟨subd7_2_46, List.forall_mem_cons.2 ⟨subd7_2_47, List.forall_mem_cons.2 ⟨subd7_2_48, List.forall_mem_cons.2 ⟨subd7_2_49, List.forall_mem_cons.2 ⟨subd7_2_50, List.forall_mem_cons.2 ⟨subd7_2_51, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C107
