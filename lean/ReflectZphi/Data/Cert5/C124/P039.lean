import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd7_12_0 : subd7_12 [-4] = true := by decide +kernel
theorem subd7_12_1 : subd7_12 [-3, -4] = true := by decide +kernel
theorem subd7_12_2 : subd7_12 [-3, -3] = true := by decide +kernel
theorem subd7_12_3 : subd7_12 [-3, -2] = true := by decide +kernel
theorem subd7_12_4 : subd7_12 [-3, -1] = true := by decide +kernel
theorem subd7_12_5 : subd7_12 [-3, 0] = true := by decide +kernel
theorem subd7_12_6 : subd7_12 [-3, 1] = true := by decide +kernel
theorem subd7_12_7 : subd7_12 [-3, 2] = true := by decide +kernel
theorem subd7_12_8 : subd7_12 [-2, -4] = true := by decide +kernel
theorem subd7_12_9 : subd7_12 [-2, -3] = true := by decide +kernel
theorem subd7_12_10 : subd7_12 [-2, -2] = true := by decide +kernel
theorem subd7_12_11 : subd7_12 [-2, -1] = true := by decide +kernel
theorem subd7_12_12 : subd7_12 [-2, 0] = true := by decide +kernel
theorem subd7_12_13 : subd7_12 [-2, 1] = true := by decide +kernel
theorem subd7_12_14 : subd7_12 [-2, 2] = true := by decide +kernel
theorem subd7_12_15 : subd7_12 [-2, 3] = true := by decide +kernel
theorem subd7_12_16 : subd7_12 [-1, -5] = true := by decide +kernel
theorem subd7_12_17 : subd7_12 [-1, -4] = true := by decide +kernel
theorem subd7_12_18 : subd7_12 [-1, -3] = true := by decide +kernel
theorem subd7_12_19 : subd7_12 [-1, -2] = true := by decide +kernel
theorem subd7_12_20 : subd7_12 [-1, -1] = true := by decide +kernel
theorem subd7_12_21 : subd7_12 [-1, 0] = true := by decide +kernel
theorem subd7_12_22 : subd7_12 [-1, 1] = true := by decide +kernel
theorem subd7_12_23 : subd7_12 [-1, 2] = true := by decide +kernel
theorem subd7_12_24 : subd7_12 [-1, 3] = true := by decide +kernel
theorem subd7_12_25 : subd7_12 [0, -5] = true := by decide +kernel
theorem subd7_12_26 : subd7_12 [0, -4] = true := by decide +kernel
theorem subd7_12_27 : subd7_12 [0, -3] = true := by decide +kernel
theorem subd7_12_28 : subd7_12 [0, -2] = true := by decide +kernel
theorem subd7_12_29 : subd7_12 [0, -1] = true := by decide +kernel
theorem subd7_12_30 : subd7_12 [0, 0] = true := by decide +kernel
theorem subd7_12_31 : subd7_12 [0, 1] = true := by decide +kernel
theorem sbd7_12_0 : ∀ q ∈ blkd7_12_0, subd7_12 q = true := by
  unfold blkd7_12_0
  exact List.forall_mem_cons.2 ⟨subd7_12_0, List.forall_mem_cons.2 ⟨subd7_12_1, List.forall_mem_cons.2 ⟨subd7_12_2, List.forall_mem_cons.2 ⟨subd7_12_3, List.forall_mem_cons.2 ⟨subd7_12_4, List.forall_mem_cons.2 ⟨subd7_12_5, List.forall_mem_cons.2 ⟨subd7_12_6, List.forall_mem_cons.2 ⟨subd7_12_7, List.forall_mem_cons.2 ⟨subd7_12_8, List.forall_mem_cons.2 ⟨subd7_12_9, List.forall_mem_cons.2 ⟨subd7_12_10, List.forall_mem_cons.2 ⟨subd7_12_11, List.forall_mem_cons.2 ⟨subd7_12_12, List.forall_mem_cons.2 ⟨subd7_12_13, List.forall_mem_cons.2 ⟨subd7_12_14, List.forall_mem_cons.2 ⟨subd7_12_15, List.forall_mem_cons.2 ⟨subd7_12_16, List.forall_mem_cons.2 ⟨subd7_12_17, List.forall_mem_cons.2 ⟨subd7_12_18, List.forall_mem_cons.2 ⟨subd7_12_19, List.forall_mem_cons.2 ⟨subd7_12_20, List.forall_mem_cons.2 ⟨subd7_12_21, List.forall_mem_cons.2 ⟨subd7_12_22, List.forall_mem_cons.2 ⟨subd7_12_23, List.forall_mem_cons.2 ⟨subd7_12_24, List.forall_mem_cons.2 ⟨subd7_12_25, List.forall_mem_cons.2 ⟨subd7_12_26, List.forall_mem_cons.2 ⟨subd7_12_27, List.forall_mem_cons.2 ⟨subd7_12_28, List.forall_mem_cons.2 ⟨subd7_12_29, List.forall_mem_cons.2 ⟨subd7_12_30, List.forall_mem_cons.2 ⟨subd7_12_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_12_32 : subd7_12 [0, 2] = true := by decide +kernel
theorem subd7_12_33 : subd7_12 [0, 3] = true := by decide +kernel
theorem subd7_12_34 : subd7_12 [0, 4] = true := by decide +kernel
theorem subd7_12_35 : subd7_12 [1, -4] = true := by decide +kernel
theorem subd7_12_36 : subd7_12 [1, -3] = true := by decide +kernel
theorem subd7_12_37 : subd7_12 [1, -2] = true := by decide +kernel
theorem subd7_12_38 : subd7_12 [1, -1] = true := by decide +kernel
theorem subd7_12_39 : subd7_12 [1, 0] = true := by decide +kernel
theorem subd7_12_40 : subd7_12 [1, 1] = true := by decide +kernel
theorem subd7_12_41 : subd7_12 [1, 2] = true := by decide +kernel
theorem subd7_12_42 : subd7_12 [1, 3] = true := by decide +kernel
theorem subd7_12_43 : subd7_12 [1, 4] = true := by decide +kernel
theorem subd7_12_44 : subd7_12 [2, -4] = true := by decide +kernel
theorem subd7_12_45 : subd7_12 [2, -3] = true := by decide +kernel
theorem subd7_12_46 : subd7_12 [2, -2] = true := by decide +kernel
theorem subd7_12_47 : subd7_12 [2, -1] = true := by decide +kernel
theorem subd7_12_48 : subd7_12 [2, 0] = true := by decide +kernel
theorem subd7_12_49 : subd7_12 [2, 1] = true := by decide +kernel
theorem subd7_12_50 : subd7_12 [2, 2] = true := by decide +kernel
theorem subd7_12_51 : subd7_12 [2, 3] = true := by decide +kernel
theorem subd7_12_52 : subd7_12 [3, -3] = true := by decide +kernel
theorem subd7_12_53 : subd7_12 [3, -2] = true := by decide +kernel
theorem subd7_12_54 : subd7_12 [3, -1] = true := by decide +kernel
theorem subd7_12_55 : subd7_12 [3, 0] = true := by decide +kernel
theorem subd7_12_56 : subd7_12 [3, 1] = true := by decide +kernel
theorem subd7_12_57 : subd7_12 [3, 2] = true := by decide +kernel
theorem subd7_12_58 : subd7_12 [3, 3] = true := by decide +kernel
theorem subd7_12_59 : subd7_12 [4] = true := by decide +kernel
theorem sbd7_12_1 : ∀ q ∈ blkd7_12_1, subd7_12 q = true := by
  unfold blkd7_12_1
  exact List.forall_mem_cons.2 ⟨subd7_12_32, List.forall_mem_cons.2 ⟨subd7_12_33, List.forall_mem_cons.2 ⟨subd7_12_34, List.forall_mem_cons.2 ⟨subd7_12_35, List.forall_mem_cons.2 ⟨subd7_12_36, List.forall_mem_cons.2 ⟨subd7_12_37, List.forall_mem_cons.2 ⟨subd7_12_38, List.forall_mem_cons.2 ⟨subd7_12_39, List.forall_mem_cons.2 ⟨subd7_12_40, List.forall_mem_cons.2 ⟨subd7_12_41, List.forall_mem_cons.2 ⟨subd7_12_42, List.forall_mem_cons.2 ⟨subd7_12_43, List.forall_mem_cons.2 ⟨subd7_12_44, List.forall_mem_cons.2 ⟨subd7_12_45, List.forall_mem_cons.2 ⟨subd7_12_46, List.forall_mem_cons.2 ⟨subd7_12_47, List.forall_mem_cons.2 ⟨subd7_12_48, List.forall_mem_cons.2 ⟨subd7_12_49, List.forall_mem_cons.2 ⟨subd7_12_50, List.forall_mem_cons.2 ⟨subd7_12_51, List.forall_mem_cons.2 ⟨subd7_12_52, List.forall_mem_cons.2 ⟨subd7_12_53, List.forall_mem_cons.2 ⟨subd7_12_54, List.forall_mem_cons.2 ⟨subd7_12_55, List.forall_mem_cons.2 ⟨subd7_12_56, List.forall_mem_cons.2 ⟨subd7_12_57, List.forall_mem_cons.2 ⟨subd7_12_58, List.forall_mem_cons.2 ⟨subd7_12_59, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_13 : ldCheck G d7_13.U d7_13.ms ldd7_13 = true := by decide +kernel
theorem pre_okd7_13 : subPre G cell7 d7_13 = true := by decide +kernel
theorem subd7_13_0 : subd7_13 [-3] = true := by decide +kernel
theorem subd7_13_1 : subd7_13 [-2, -3] = true := by decide +kernel
theorem subd7_13_2 : subd7_13 [-2, -2] = true := by decide +kernel
theorem subd7_13_3 : subd7_13 [-2, -1] = true := by decide +kernel
theorem subd7_13_4 : subd7_13 [-2, 0] = true := by decide +kernel
theorem subd7_13_5 : subd7_13 [-2, 1] = true := by decide +kernel
theorem subd7_13_6 : subd7_13 [-2, 2] = true := by decide +kernel
theorem subd7_13_7 : subd7_13 [-2, 3] = true := by decide +kernel
theorem subd7_13_8 : subd7_13 [-2, 4] = true := by decide +kernel
theorem subd7_13_9 : subd7_13 [-1, -4] = true := by decide +kernel
theorem subd7_13_10 : subd7_13 [-1, -3] = true := by decide +kernel
theorem subd7_13_11 : subd7_13 [-1, -2] = true := by decide +kernel
theorem subd7_13_12 : subd7_13 [-1, -1] = true := by decide +kernel
theorem subd7_13_13 : subd7_13 [-1, 0] = true := by decide +kernel
theorem subd7_13_14 : subd7_13 [-1, 1] = true := by decide +kernel
theorem subd7_13_15 : subd7_13 [-1, 2] = true := by decide +kernel
theorem subd7_13_16 : subd7_13 [-1, 3] = true := by decide +kernel
theorem subd7_13_17 : subd7_13 [-1, 4] = true := by decide +kernel
theorem subd7_13_18 : subd7_13 [0, -5] = true := by decide +kernel
theorem subd7_13_19 : subd7_13 [0, -4] = true := by decide +kernel
theorem subd7_13_20 : subd7_13 [0, -3] = true := by decide +kernel
theorem subd7_13_21 : subd7_13 [0, -2] = true := by decide +kernel
theorem subd7_13_22 : subd7_13 [0, -1] = true := by decide +kernel
theorem subd7_13_23 : subd7_13 [0, 0] = true := by decide +kernel
theorem subd7_13_24 : subd7_13 [0, 1] = true := by decide +kernel
theorem subd7_13_25 : subd7_13 [0, 2] = true := by decide +kernel
theorem subd7_13_26 : subd7_13 [0, 3] = true := by decide +kernel
theorem subd7_13_27 : subd7_13 [0, 4] = true := by decide +kernel
theorem subd7_13_28 : subd7_13 [1, -5] = true := by decide +kernel
theorem subd7_13_29 : subd7_13 [1, -4] = true := by decide +kernel
theorem subd7_13_30 : subd7_13 [1, -3] = true := by decide +kernel
theorem subd7_13_31 : subd7_13 [1, -2] = true := by decide +kernel
theorem sbd7_13_0 : ∀ q ∈ blkd7_13_0, subd7_13 q = true := by
  unfold blkd7_13_0
  exact List.forall_mem_cons.2 ⟨subd7_13_0, List.forall_mem_cons.2 ⟨subd7_13_1, List.forall_mem_cons.2 ⟨subd7_13_2, List.forall_mem_cons.2 ⟨subd7_13_3, List.forall_mem_cons.2 ⟨subd7_13_4, List.forall_mem_cons.2 ⟨subd7_13_5, List.forall_mem_cons.2 ⟨subd7_13_6, List.forall_mem_cons.2 ⟨subd7_13_7, List.forall_mem_cons.2 ⟨subd7_13_8, List.forall_mem_cons.2 ⟨subd7_13_9, List.forall_mem_cons.2 ⟨subd7_13_10, List.forall_mem_cons.2 ⟨subd7_13_11, List.forall_mem_cons.2 ⟨subd7_13_12, List.forall_mem_cons.2 ⟨subd7_13_13, List.forall_mem_cons.2 ⟨subd7_13_14, List.forall_mem_cons.2 ⟨subd7_13_15, List.forall_mem_cons.2 ⟨subd7_13_16, List.forall_mem_cons.2 ⟨subd7_13_17, List.forall_mem_cons.2 ⟨subd7_13_18, List.forall_mem_cons.2 ⟨subd7_13_19, List.forall_mem_cons.2 ⟨subd7_13_20, List.forall_mem_cons.2 ⟨subd7_13_21, List.forall_mem_cons.2 ⟨subd7_13_22, List.forall_mem_cons.2 ⟨subd7_13_23, List.forall_mem_cons.2 ⟨subd7_13_24, List.forall_mem_cons.2 ⟨subd7_13_25, List.forall_mem_cons.2 ⟨subd7_13_26, List.forall_mem_cons.2 ⟨subd7_13_27, List.forall_mem_cons.2 ⟨subd7_13_28, List.forall_mem_cons.2 ⟨subd7_13_29, List.forall_mem_cons.2 ⟨subd7_13_30, List.forall_mem_cons.2 ⟨subd7_13_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_13_32 : subd7_13 [1, -1] = true := by decide +kernel
theorem subd7_13_33 : subd7_13 [1, 0] = true := by decide +kernel
theorem subd7_13_34 : subd7_13 [1, 1] = true := by decide +kernel
theorem subd7_13_35 : subd7_13 [1, 2] = true := by decide +kernel
theorem subd7_13_36 : subd7_13 [1, 3] = true := by decide +kernel
theorem subd7_13_37 : subd7_13 [2, -5] = true := by decide +kernel
theorem subd7_13_38 : subd7_13 [2, -4] = true := by decide +kernel
theorem subd7_13_39 : subd7_13 [2, -3] = true := by decide +kernel
theorem subd7_13_40 : subd7_13 [2, -2] = true := by decide +kernel
theorem subd7_13_41 : subd7_13 [2, -1] = true := by decide +kernel
theorem subd7_13_42 : subd7_13 [2, 0] = true := by decide +kernel
theorem subd7_13_43 : subd7_13 [2, 1] = true := by decide +kernel
theorem subd7_13_44 : subd7_13 [2, 2] = true := by decide +kernel
theorem subd7_13_45 : subd7_13 [3] = true := by decide +kernel
theorem sbd7_13_1 : ∀ q ∈ blkd7_13_1, subd7_13 q = true := by
  unfold blkd7_13_1
  exact List.forall_mem_cons.2 ⟨subd7_13_32, List.forall_mem_cons.2 ⟨subd7_13_33, List.forall_mem_cons.2 ⟨subd7_13_34, List.forall_mem_cons.2 ⟨subd7_13_35, List.forall_mem_cons.2 ⟨subd7_13_36, List.forall_mem_cons.2 ⟨subd7_13_37, List.forall_mem_cons.2 ⟨subd7_13_38, List.forall_mem_cons.2 ⟨subd7_13_39, List.forall_mem_cons.2 ⟨subd7_13_40, List.forall_mem_cons.2 ⟨subd7_13_41, List.forall_mem_cons.2 ⟨subd7_13_42, List.forall_mem_cons.2 ⟨subd7_13_43, List.forall_mem_cons.2 ⟨subd7_13_44, List.forall_mem_cons.2 ⟨subd7_13_45, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_14 : ldCheck G d7_14.U d7_14.ms ldd7_14 = true := by decide +kernel
theorem pre_okd7_14 : subPre G cell7 d7_14 = true := by decide +kernel
theorem subd7_14_0 : subd7_14 [-4, -3] = true := by decide +kernel
theorem subd7_14_1 : subd7_14 [-4, -2] = true := by decide +kernel
theorem subd7_14_2 : subd7_14 [-4, -1] = true := by decide +kernel
theorem subd7_14_3 : subd7_14 [-4, 0] = true := by decide +kernel
theorem subd7_14_4 : subd7_14 [-4, 1] = true := by decide +kernel
theorem subd7_14_5 : subd7_14 [-3, -4] = true := by decide +kernel
theorem subd7_14_6 : subd7_14 [-3, -3] = true := by decide +kernel
theorem subd7_14_7 : subd7_14 [-3, -2, -8] = true := by decide +kernel
theorem subd7_14_8 : subd7_14 [-3, -2, -7] = true := by decide +kernel
theorem subd7_14_9 : subd7_14 [-3, -2, -6] = true := by decide +kernel
theorem subd7_14_10 : subd7_14 [-3, -2, -5] = true := by decide +kernel
theorem subd7_14_11 : subd7_14 [-3, -2, -4] = true := by decide +kernel
theorem subd7_14_12 : subd7_14 [-3, -2, -3] = true := by decide +kernel
theorem subd7_14_13 : subd7_14 [-3, -2, -2] = true := by decide +kernel
theorem subd7_14_14 : subd7_14 [-3, -2, -1] = true := by decide +kernel
theorem subd7_14_15 : subd7_14 [-3, -2, 0] = true := by decide +kernel
theorem subd7_14_16 : subd7_14 [-3, -2, 1] = true := by decide +kernel
theorem subd7_14_17 : subd7_14 [-3, -2, 2] = true := by decide +kernel
theorem subd7_14_18 : subd7_14 [-3, -2, 3] = true := by decide +kernel
theorem subd7_14_19 : subd7_14 [-3, -2, 4] = true := by decide +kernel
theorem subd7_14_20 : subd7_14 [-3, -2, 5] = true := by decide +kernel
theorem subd7_14_21 : subd7_14 [-3, -2, 6] = true := by decide +kernel
theorem subd7_14_22 : subd7_14 [-3, -1, -9] = true := by decide +kernel
theorem subd7_14_23 : subd7_14 [-3, -1, -8] = true := by decide +kernel
theorem subd7_14_24 : subd7_14 [-3, -1, -7] = true := by decide +kernel
theorem subd7_14_25 : subd7_14 [-3, -1, -6] = true := by decide +kernel
theorem subd7_14_26 : subd7_14 [-3, -1, -5] = true := by decide +kernel
theorem subd7_14_27 : subd7_14 [-3, -1, -4] = true := by decide +kernel
theorem subd7_14_28 : subd7_14 [-3, -1, -3] = true := by decide +kernel
theorem subd7_14_29 : subd7_14 [-3, -1, -2] = true := by decide +kernel
theorem subd7_14_30 : subd7_14 [-3, -1, -1] = true := by decide +kernel
theorem subd7_14_31 : subd7_14 [-3, -1, 0] = true := by decide +kernel
theorem sbd7_14_0 : ∀ q ∈ blkd7_14_0, subd7_14 q = true := by
  unfold blkd7_14_0
  exact List.forall_mem_cons.2 ⟨subd7_14_0, List.forall_mem_cons.2 ⟨subd7_14_1, List.forall_mem_cons.2 ⟨subd7_14_2, List.forall_mem_cons.2 ⟨subd7_14_3, List.forall_mem_cons.2 ⟨subd7_14_4, List.forall_mem_cons.2 ⟨subd7_14_5, List.forall_mem_cons.2 ⟨subd7_14_6, List.forall_mem_cons.2 ⟨subd7_14_7, List.forall_mem_cons.2 ⟨subd7_14_8, List.forall_mem_cons.2 ⟨subd7_14_9, List.forall_mem_cons.2 ⟨subd7_14_10, List.forall_mem_cons.2 ⟨subd7_14_11, List.forall_mem_cons.2 ⟨subd7_14_12, List.forall_mem_cons.2 ⟨subd7_14_13, List.forall_mem_cons.2 ⟨subd7_14_14, List.forall_mem_cons.2 ⟨subd7_14_15, List.forall_mem_cons.2 ⟨subd7_14_16, List.forall_mem_cons.2 ⟨subd7_14_17, List.forall_mem_cons.2 ⟨subd7_14_18, List.forall_mem_cons.2 ⟨subd7_14_19, List.forall_mem_cons.2 ⟨subd7_14_20, List.forall_mem_cons.2 ⟨subd7_14_21, List.forall_mem_cons.2 ⟨subd7_14_22, List.forall_mem_cons.2 ⟨subd7_14_23, List.forall_mem_cons.2 ⟨subd7_14_24, List.forall_mem_cons.2 ⟨subd7_14_25, List.forall_mem_cons.2 ⟨subd7_14_26, List.forall_mem_cons.2 ⟨subd7_14_27, List.forall_mem_cons.2 ⟨subd7_14_28, List.forall_mem_cons.2 ⟨subd7_14_29, List.forall_mem_cons.2 ⟨subd7_14_30, List.forall_mem_cons.2 ⟨subd7_14_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_14_32 : subd7_14 [-3, -1, 1] = true := by decide +kernel
theorem subd7_14_33 : subd7_14 [-3, -1, 2] = true := by decide +kernel
theorem subd7_14_34 : subd7_14 [-3, -1, 3] = true := by decide +kernel
theorem subd7_14_35 : subd7_14 [-3, -1, 4] = true := by decide +kernel
theorem subd7_14_36 : subd7_14 [-3, -1, 5] = true := by decide +kernel
theorem subd7_14_37 : subd7_14 [-3, -1, 6] = true := by decide +kernel
theorem subd7_14_38 : subd7_14 [-3, -1, 7] = true := by decide +kernel
theorem subd7_14_39 : subd7_14 [-3, 0, -9] = true := by decide +kernel
theorem subd7_14_40 : subd7_14 [-3, 0, -8] = true := by decide +kernel
theorem subd7_14_41 : subd7_14 [-3, 0, -7] = true := by decide +kernel
theorem subd7_14_42 : subd7_14 [-3, 0, -6] = true := by decide +kernel
theorem subd7_14_43 : subd7_14 [-3, 0, -5] = true := by decide +kernel
theorem subd7_14_44 : subd7_14 [-3, 0, -4] = true := by decide +kernel
theorem subd7_14_45 : subd7_14 [-3, 0, -3] = true := by decide +kernel
theorem subd7_14_46 : subd7_14 [-3, 0, -2] = true := by decide +kernel
theorem subd7_14_47 : subd7_14 [-3, 0, -1] = true := by decide +kernel
theorem subd7_14_48 : subd7_14 [-3, 0, 0] = true := by decide +kernel
theorem subd7_14_49 : subd7_14 [-3, 0, 1] = true := by decide +kernel
theorem subd7_14_50 : subd7_14 [-3, 0, 2] = true := by decide +kernel
theorem subd7_14_51 : subd7_14 [-3, 0, 3] = true := by decide +kernel
theorem subd7_14_52 : subd7_14 [-3, 0, 4] = true := by decide +kernel
theorem subd7_14_53 : subd7_14 [-3, 0, 5] = true := by decide +kernel
theorem subd7_14_54 : subd7_14 [-3, 0, 6] = true := by decide +kernel
theorem subd7_14_55 : subd7_14 [-3, 0, 7] = true := by decide +kernel
theorem subd7_14_56 : subd7_14 [-3, 1, -9] = true := by decide +kernel
theorem subd7_14_57 : subd7_14 [-3, 1, -8] = true := by decide +kernel
theorem subd7_14_58 : subd7_14 [-3, 1, -7] = true := by decide +kernel
theorem subd7_14_59 : subd7_14 [-3, 1, -6] = true := by decide +kernel
theorem subd7_14_60 : subd7_14 [-3, 1, -5] = true := by decide +kernel
theorem subd7_14_61 : subd7_14 [-3, 1, -4] = true := by decide +kernel
theorem subd7_14_62 : subd7_14 [-3, 1, -3] = true := by decide +kernel
theorem subd7_14_63 : subd7_14 [-3, 1, -2] = true := by decide +kernel
theorem sbd7_14_1 : ∀ q ∈ blkd7_14_1, subd7_14 q = true := by
  unfold blkd7_14_1
  exact List.forall_mem_cons.2 ⟨subd7_14_32, List.forall_mem_cons.2 ⟨subd7_14_33, List.forall_mem_cons.2 ⟨subd7_14_34, List.forall_mem_cons.2 ⟨subd7_14_35, List.forall_mem_cons.2 ⟨subd7_14_36, List.forall_mem_cons.2 ⟨subd7_14_37, List.forall_mem_cons.2 ⟨subd7_14_38, List.forall_mem_cons.2 ⟨subd7_14_39, List.forall_mem_cons.2 ⟨subd7_14_40, List.forall_mem_cons.2 ⟨subd7_14_41, List.forall_mem_cons.2 ⟨subd7_14_42, List.forall_mem_cons.2 ⟨subd7_14_43, List.forall_mem_cons.2 ⟨subd7_14_44, List.forall_mem_cons.2 ⟨subd7_14_45, List.forall_mem_cons.2 ⟨subd7_14_46, List.forall_mem_cons.2 ⟨subd7_14_47, List.forall_mem_cons.2 ⟨subd7_14_48, List.forall_mem_cons.2 ⟨subd7_14_49, List.forall_mem_cons.2 ⟨subd7_14_50, List.forall_mem_cons.2 ⟨subd7_14_51, List.forall_mem_cons.2 ⟨subd7_14_52, List.forall_mem_cons.2 ⟨subd7_14_53, List.forall_mem_cons.2 ⟨subd7_14_54, List.forall_mem_cons.2 ⟨subd7_14_55, List.forall_mem_cons.2 ⟨subd7_14_56, List.forall_mem_cons.2 ⟨subd7_14_57, List.forall_mem_cons.2 ⟨subd7_14_58, List.forall_mem_cons.2 ⟨subd7_14_59, List.forall_mem_cons.2 ⟨subd7_14_60, List.forall_mem_cons.2 ⟨subd7_14_61, List.forall_mem_cons.2 ⟨subd7_14_62, List.forall_mem_cons.2 ⟨subd7_14_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_14_64 : subd7_14 [-3, 1, -1] = true := by decide +kernel
theorem subd7_14_65 : subd7_14 [-3, 1, 0] = true := by decide +kernel
theorem subd7_14_66 : subd7_14 [-3, 1, 1] = true := by decide +kernel
theorem subd7_14_67 : subd7_14 [-3, 1, 2] = true := by decide +kernel
theorem subd7_14_68 : subd7_14 [-3, 1, 3] = true := by decide +kernel
theorem subd7_14_69 : subd7_14 [-3, 1, 4] = true := by decide +kernel
theorem subd7_14_70 : subd7_14 [-3, 1, 5] = true := by decide +kernel
theorem subd7_14_71 : subd7_14 [-3, 1, 6] = true := by decide +kernel
theorem subd7_14_72 : subd7_14 [-3, 2] = true := by decide +kernel
theorem subd7_14_73 : subd7_14 [-3, 3] = true := by decide +kernel
theorem subd7_14_74 : subd7_14 [-2, -5] = true := by decide +kernel
theorem subd7_14_75 : subd7_14 [-2, -4] = true := by decide +kernel
theorem subd7_14_76 : subd7_14 [-2, -3, -7] = true := by decide +kernel
theorem subd7_14_77 : subd7_14 [-2, -3, -6] = true := by decide +kernel
theorem subd7_14_78 : subd7_14 [-2, -3, -5] = true := by decide +kernel
theorem subd7_14_79 : subd7_14 [-2, -3, -4] = true := by decide +kernel
theorem subd7_14_80 : subd7_14 [-2, -3, -3] = true := by decide +kernel
theorem subd7_14_81 : subd7_14 [-2, -3, -2] = true := by decide +kernel
theorem subd7_14_82 : subd7_14 [-2, -3, -1] = true := by decide +kernel
theorem subd7_14_83 : subd7_14 [-2, -3, 0] = true := by decide +kernel
theorem subd7_14_84 : subd7_14 [-2, -3, 1] = true := by decide +kernel
theorem subd7_14_85 : subd7_14 [-2, -3, 2] = true := by decide +kernel
theorem subd7_14_86 : subd7_14 [-2, -3, 3] = true := by decide +kernel
theorem subd7_14_87 : subd7_14 [-2, -3, 4] = true := by decide +kernel
theorem subd7_14_88 : subd7_14 [-2, -3, 5] = true := by decide +kernel
theorem subd7_14_89 : subd7_14 [-2, -3, 6] = true := by decide +kernel
theorem subd7_14_90 : subd7_14 [-2, -3, 7] = true := by decide +kernel
theorem subd7_14_91 : subd7_14 [-2, -2, -9] = true := by decide +kernel
theorem subd7_14_92 : subd7_14 [-2, -2, -8] = true := by decide +kernel
theorem subd7_14_93 : subd7_14 [-2, -2, -7] = true := by decide +kernel
theorem subd7_14_94 : subd7_14 [-2, -2, -6] = true := by decide +kernel
theorem subd7_14_95 : subd7_14 [-2, -2, -5] = true := by decide +kernel
theorem sbd7_14_2 : ∀ q ∈ blkd7_14_2, subd7_14 q = true := by
  unfold blkd7_14_2
  exact List.forall_mem_cons.2 ⟨subd7_14_64, List.forall_mem_cons.2 ⟨subd7_14_65, List.forall_mem_cons.2 ⟨subd7_14_66, List.forall_mem_cons.2 ⟨subd7_14_67, List.forall_mem_cons.2 ⟨subd7_14_68, List.forall_mem_cons.2 ⟨subd7_14_69, List.forall_mem_cons.2 ⟨subd7_14_70, List.forall_mem_cons.2 ⟨subd7_14_71, List.forall_mem_cons.2 ⟨subd7_14_72, List.forall_mem_cons.2 ⟨subd7_14_73, List.forall_mem_cons.2 ⟨subd7_14_74, List.forall_mem_cons.2 ⟨subd7_14_75, List.forall_mem_cons.2 ⟨subd7_14_76, List.forall_mem_cons.2 ⟨subd7_14_77, List.forall_mem_cons.2 ⟨subd7_14_78, List.forall_mem_cons.2 ⟨subd7_14_79, List.forall_mem_cons.2 ⟨subd7_14_80, List.forall_mem_cons.2 ⟨subd7_14_81, List.forall_mem_cons.2 ⟨subd7_14_82, List.forall_mem_cons.2 ⟨subd7_14_83, List.forall_mem_cons.2 ⟨subd7_14_84, List.forall_mem_cons.2 ⟨subd7_14_85, List.forall_mem_cons.2 ⟨subd7_14_86, List.forall_mem_cons.2 ⟨subd7_14_87, List.forall_mem_cons.2 ⟨subd7_14_88, List.forall_mem_cons.2 ⟨subd7_14_89, List.forall_mem_cons.2 ⟨subd7_14_90, List.forall_mem_cons.2 ⟨subd7_14_91, List.forall_mem_cons.2 ⟨subd7_14_92, List.forall_mem_cons.2 ⟨subd7_14_93, List.forall_mem_cons.2 ⟨subd7_14_94, List.forall_mem_cons.2 ⟨subd7_14_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C124
