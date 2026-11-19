import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd21_2_32 : subd21_2 [2, -4] = true := by decide +kernel
theorem subd21_2_33 : subd21_2 [2, -3] = true := by decide +kernel
theorem subd21_2_34 : subd21_2 [2, -2] = true := by decide +kernel
theorem subd21_2_35 : subd21_2 [2, -1] = true := by decide +kernel
theorem subd21_2_36 : subd21_2 [2, 0] = true := by decide +kernel
theorem subd21_2_37 : subd21_2 [2, 1] = true := by decide +kernel
theorem subd21_2_38 : subd21_2 [2, 2] = true := by decide +kernel
theorem subd21_2_39 : subd21_2 [3] = true := by decide +kernel
theorem sbd21_2_1 : ∀ q ∈ blkd21_2_1, subd21_2 q = true := by
  unfold blkd21_2_1
  exact List.forall_mem_cons.2 ⟨subd21_2_32, List.forall_mem_cons.2 ⟨subd21_2_33, List.forall_mem_cons.2 ⟨subd21_2_34, List.forall_mem_cons.2 ⟨subd21_2_35, List.forall_mem_cons.2 ⟨subd21_2_36, List.forall_mem_cons.2 ⟨subd21_2_37, List.forall_mem_cons.2 ⟨subd21_2_38, List.forall_mem_cons.2 ⟨subd21_2_39, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd21_3 : ldCheck G d21_3.U d21_3.ms ldd21_3 = true := by decide +kernel
theorem pre_okd21_3 : subPre G cell21 d21_3 = true := by decide +kernel
theorem subd21_3_0 : subd21_3 [-4] = true := by decide +kernel
theorem subd21_3_1 : subd21_3 [-3, -5] = true := by decide +kernel
theorem subd21_3_2 : subd21_3 [-3, -4] = true := by decide +kernel
theorem subd21_3_3 : subd21_3 [-3, -3] = true := by decide +kernel
theorem subd21_3_4 : subd21_3 [-3, -2] = true := by decide +kernel
theorem subd21_3_5 : subd21_3 [-3, -1] = true := by decide +kernel
theorem subd21_3_6 : subd21_3 [-3, 0] = true := by decide +kernel
theorem subd21_3_7 : subd21_3 [-3, 1] = true := by decide +kernel
theorem subd21_3_8 : subd21_3 [-2, -5] = true := by decide +kernel
theorem subd21_3_9 : subd21_3 [-2, -4] = true := by decide +kernel
theorem subd21_3_10 : subd21_3 [-2, -3] = true := by decide +kernel
theorem subd21_3_11 : subd21_3 [-2, -2] = true := by decide +kernel
theorem subd21_3_12 : subd21_3 [-2, -1] = true := by decide +kernel
theorem subd21_3_13 : subd21_3 [-2, 0] = true := by decide +kernel
theorem subd21_3_14 : subd21_3 [-2, 1] = true := by decide +kernel
theorem subd21_3_15 : subd21_3 [-2, 2] = true := by decide +kernel
theorem subd21_3_16 : subd21_3 [-1, -5] = true := by decide +kernel
theorem subd21_3_17 : subd21_3 [-1, -4] = true := by decide +kernel
theorem subd21_3_18 : subd21_3 [-1, -3] = true := by decide +kernel
theorem subd21_3_19 : subd21_3 [-1, -2] = true := by decide +kernel
theorem subd21_3_20 : subd21_3 [-1, -1] = true := by decide +kernel
theorem subd21_3_21 : subd21_3 [-1, 0] = true := by decide +kernel
theorem subd21_3_22 : subd21_3 [-1, 1] = true := by decide +kernel
theorem subd21_3_23 : subd21_3 [-1, 2] = true := by decide +kernel
theorem subd21_3_24 : subd21_3 [-1, 3] = true := by decide +kernel
theorem subd21_3_25 : subd21_3 [0, -5] = true := by decide +kernel
theorem subd21_3_26 : subd21_3 [0, -4] = true := by decide +kernel
theorem subd21_3_27 : subd21_3 [0, -3] = true := by decide +kernel
theorem subd21_3_28 : subd21_3 [0, -2] = true := by decide +kernel
theorem subd21_3_29 : subd21_3 [0, -1] = true := by decide +kernel
theorem subd21_3_30 : subd21_3 [0, 0] = true := by decide +kernel
theorem subd21_3_31 : subd21_3 [0, 1] = true := by decide +kernel
theorem sbd21_3_0 : ∀ q ∈ blkd21_3_0, subd21_3 q = true := by
  unfold blkd21_3_0
  exact List.forall_mem_cons.2 ⟨subd21_3_0, List.forall_mem_cons.2 ⟨subd21_3_1, List.forall_mem_cons.2 ⟨subd21_3_2, List.forall_mem_cons.2 ⟨subd21_3_3, List.forall_mem_cons.2 ⟨subd21_3_4, List.forall_mem_cons.2 ⟨subd21_3_5, List.forall_mem_cons.2 ⟨subd21_3_6, List.forall_mem_cons.2 ⟨subd21_3_7, List.forall_mem_cons.2 ⟨subd21_3_8, List.forall_mem_cons.2 ⟨subd21_3_9, List.forall_mem_cons.2 ⟨subd21_3_10, List.forall_mem_cons.2 ⟨subd21_3_11, List.forall_mem_cons.2 ⟨subd21_3_12, List.forall_mem_cons.2 ⟨subd21_3_13, List.forall_mem_cons.2 ⟨subd21_3_14, List.forall_mem_cons.2 ⟨subd21_3_15, List.forall_mem_cons.2 ⟨subd21_3_16, List.forall_mem_cons.2 ⟨subd21_3_17, List.forall_mem_cons.2 ⟨subd21_3_18, List.forall_mem_cons.2 ⟨subd21_3_19, List.forall_mem_cons.2 ⟨subd21_3_20, List.forall_mem_cons.2 ⟨subd21_3_21, List.forall_mem_cons.2 ⟨subd21_3_22, List.forall_mem_cons.2 ⟨subd21_3_23, List.forall_mem_cons.2 ⟨subd21_3_24, List.forall_mem_cons.2 ⟨subd21_3_25, List.forall_mem_cons.2 ⟨subd21_3_26, List.forall_mem_cons.2 ⟨subd21_3_27, List.forall_mem_cons.2 ⟨subd21_3_28, List.forall_mem_cons.2 ⟨subd21_3_29, List.forall_mem_cons.2 ⟨subd21_3_30, List.forall_mem_cons.2 ⟨subd21_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd21_3_32 : subd21_3 [0, 2] = true := by decide +kernel
theorem subd21_3_33 : subd21_3 [0, 3] = true := by decide +kernel
theorem subd21_3_34 : subd21_3 [0, 4] = true := by decide +kernel
theorem subd21_3_35 : subd21_3 [1, -4] = true := by decide +kernel
theorem subd21_3_36 : subd21_3 [1, -3] = true := by decide +kernel
theorem subd21_3_37 : subd21_3 [1, -2] = true := by decide +kernel
theorem subd21_3_38 : subd21_3 [1, -1] = true := by decide +kernel
theorem subd21_3_39 : subd21_3 [1, 0] = true := by decide +kernel
theorem subd21_3_40 : subd21_3 [1, 1] = true := by decide +kernel
theorem subd21_3_41 : subd21_3 [1, 2] = true := by decide +kernel
theorem subd21_3_42 : subd21_3 [1, 3] = true := by decide +kernel
theorem subd21_3_43 : subd21_3 [1, 4] = true := by decide +kernel
theorem subd21_3_44 : subd21_3 [2, -3] = true := by decide +kernel
theorem subd21_3_45 : subd21_3 [2, -2] = true := by decide +kernel
theorem subd21_3_46 : subd21_3 [2, -1] = true := by decide +kernel
theorem subd21_3_47 : subd21_3 [2, 0] = true := by decide +kernel
theorem subd21_3_48 : subd21_3 [2, 1] = true := by decide +kernel
theorem subd21_3_49 : subd21_3 [2, 2] = true := by decide +kernel
theorem subd21_3_50 : subd21_3 [2, 3] = true := by decide +kernel
theorem subd21_3_51 : subd21_3 [2, 4] = true := by decide +kernel
theorem subd21_3_52 : subd21_3 [3, -2] = true := by decide +kernel
theorem subd21_3_53 : subd21_3 [3, -1] = true := by decide +kernel
theorem subd21_3_54 : subd21_3 [3, 0] = true := by decide +kernel
theorem subd21_3_55 : subd21_3 [3, 1] = true := by decide +kernel
theorem subd21_3_56 : subd21_3 [3, 2] = true := by decide +kernel
theorem subd21_3_57 : subd21_3 [3, 3] = true := by decide +kernel
theorem subd21_3_58 : subd21_3 [3, 4] = true := by decide +kernel
theorem subd21_3_59 : subd21_3 [4] = true := by decide +kernel
theorem sbd21_3_1 : ∀ q ∈ blkd21_3_1, subd21_3 q = true := by
  unfold blkd21_3_1
  exact List.forall_mem_cons.2 ⟨subd21_3_32, List.forall_mem_cons.2 ⟨subd21_3_33, List.forall_mem_cons.2 ⟨subd21_3_34, List.forall_mem_cons.2 ⟨subd21_3_35, List.forall_mem_cons.2 ⟨subd21_3_36, List.forall_mem_cons.2 ⟨subd21_3_37, List.forall_mem_cons.2 ⟨subd21_3_38, List.forall_mem_cons.2 ⟨subd21_3_39, List.forall_mem_cons.2 ⟨subd21_3_40, List.forall_mem_cons.2 ⟨subd21_3_41, List.forall_mem_cons.2 ⟨subd21_3_42, List.forall_mem_cons.2 ⟨subd21_3_43, List.forall_mem_cons.2 ⟨subd21_3_44, List.forall_mem_cons.2 ⟨subd21_3_45, List.forall_mem_cons.2 ⟨subd21_3_46, List.forall_mem_cons.2 ⟨subd21_3_47, List.forall_mem_cons.2 ⟨subd21_3_48, List.forall_mem_cons.2 ⟨subd21_3_49, List.forall_mem_cons.2 ⟨subd21_3_50, List.forall_mem_cons.2 ⟨subd21_3_51, List.forall_mem_cons.2 ⟨subd21_3_52, List.forall_mem_cons.2 ⟨subd21_3_53, List.forall_mem_cons.2 ⟨subd21_3_54, List.forall_mem_cons.2 ⟨subd21_3_55, List.forall_mem_cons.2 ⟨subd21_3_56, List.forall_mem_cons.2 ⟨subd21_3_57, List.forall_mem_cons.2 ⟨subd21_3_58, List.forall_mem_cons.2 ⟨subd21_3_59, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd22_0 : ldCheck G d22_0.U d22_0.ms ldd22_0 = true := by decide +kernel
theorem pre_okd22_0 : subPre G cell22 d22_0 = true := by decide +kernel
theorem subd22_0_0 : subd22_0 [-3] = true := by decide +kernel
theorem subd22_0_1 : subd22_0 [-2, -3] = true := by decide +kernel
theorem subd22_0_2 : subd22_0 [-2, -2] = true := by decide +kernel
theorem subd22_0_3 : subd22_0 [-2, -1] = true := by decide +kernel
theorem subd22_0_4 : subd22_0 [-2, 0] = true := by decide +kernel
theorem subd22_0_5 : subd22_0 [-2, 1] = true := by decide +kernel
theorem subd22_0_6 : subd22_0 [-2, 2] = true := by decide +kernel
theorem subd22_0_7 : subd22_0 [-1, -4] = true := by decide +kernel
theorem subd22_0_8 : subd22_0 [-1, -3] = true := by decide +kernel
theorem subd22_0_9 : subd22_0 [-1, -2] = true := by decide +kernel
theorem subd22_0_10 : subd22_0 [-1, -1] = true := by decide +kernel
theorem subd22_0_11 : subd22_0 [-1, 0] = true := by decide +kernel
theorem subd22_0_12 : subd22_0 [-1, 1] = true := by decide +kernel
theorem subd22_0_13 : subd22_0 [-1, 2] = true := by decide +kernel
theorem subd22_0_14 : subd22_0 [-1, 3] = true := by decide +kernel
theorem subd22_0_15 : subd22_0 [0, -4] = true := by decide +kernel
theorem subd22_0_16 : subd22_0 [0, -3] = true := by decide +kernel
theorem subd22_0_17 : subd22_0 [0, -2] = true := by decide +kernel
theorem subd22_0_18 : subd22_0 [0, -1] = true := by decide +kernel
theorem subd22_0_19 : subd22_0 [0, 0] = true := by decide +kernel
theorem subd22_0_20 : subd22_0 [0, 1] = true := by decide +kernel
theorem subd22_0_21 : subd22_0 [0, 2] = true := by decide +kernel
theorem subd22_0_22 : subd22_0 [0, 3] = true := by decide +kernel
theorem subd22_0_23 : subd22_0 [1, -4] = true := by decide +kernel
theorem subd22_0_24 : subd22_0 [1, -3] = true := by decide +kernel
theorem subd22_0_25 : subd22_0 [1, -2] = true := by decide +kernel
theorem subd22_0_26 : subd22_0 [1, -1] = true := by decide +kernel
theorem subd22_0_27 : subd22_0 [1, 0] = true := by decide +kernel
theorem subd22_0_28 : subd22_0 [1, 1] = true := by decide +kernel
theorem subd22_0_29 : subd22_0 [1, 2] = true := by decide +kernel
theorem subd22_0_30 : subd22_0 [1, 3] = true := by decide +kernel
theorem subd22_0_31 : subd22_0 [2, -3] = true := by decide +kernel
theorem sbd22_0_0 : ∀ q ∈ blkd22_0_0, subd22_0 q = true := by
  unfold blkd22_0_0
  exact List.forall_mem_cons.2 ⟨subd22_0_0, List.forall_mem_cons.2 ⟨subd22_0_1, List.forall_mem_cons.2 ⟨subd22_0_2, List.forall_mem_cons.2 ⟨subd22_0_3, List.forall_mem_cons.2 ⟨subd22_0_4, List.forall_mem_cons.2 ⟨subd22_0_5, List.forall_mem_cons.2 ⟨subd22_0_6, List.forall_mem_cons.2 ⟨subd22_0_7, List.forall_mem_cons.2 ⟨subd22_0_8, List.forall_mem_cons.2 ⟨subd22_0_9, List.forall_mem_cons.2 ⟨subd22_0_10, List.forall_mem_cons.2 ⟨subd22_0_11, List.forall_mem_cons.2 ⟨subd22_0_12, List.forall_mem_cons.2 ⟨subd22_0_13, List.forall_mem_cons.2 ⟨subd22_0_14, List.forall_mem_cons.2 ⟨subd22_0_15, List.forall_mem_cons.2 ⟨subd22_0_16, List.forall_mem_cons.2 ⟨subd22_0_17, List.forall_mem_cons.2 ⟨subd22_0_18, List.forall_mem_cons.2 ⟨subd22_0_19, List.forall_mem_cons.2 ⟨subd22_0_20, List.forall_mem_cons.2 ⟨subd22_0_21, List.forall_mem_cons.2 ⟨subd22_0_22, List.forall_mem_cons.2 ⟨subd22_0_23, List.forall_mem_cons.2 ⟨subd22_0_24, List.forall_mem_cons.2 ⟨subd22_0_25, List.forall_mem_cons.2 ⟨subd22_0_26, List.forall_mem_cons.2 ⟨subd22_0_27, List.forall_mem_cons.2 ⟨subd22_0_28, List.forall_mem_cons.2 ⟨subd22_0_29, List.forall_mem_cons.2 ⟨subd22_0_30, List.forall_mem_cons.2 ⟨subd22_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd22_0_32 : subd22_0 [2, -2] = true := by decide +kernel
theorem subd22_0_33 : subd22_0 [2, -1] = true := by decide +kernel
theorem subd22_0_34 : subd22_0 [2, 0] = true := by decide +kernel
theorem subd22_0_35 : subd22_0 [2, 1] = true := by decide +kernel
theorem subd22_0_36 : subd22_0 [2, 2] = true := by decide +kernel
theorem subd22_0_37 : subd22_0 [3] = true := by decide +kernel
theorem sbd22_0_1 : ∀ q ∈ blkd22_0_1, subd22_0 q = true := by
  unfold blkd22_0_1
  exact List.forall_mem_cons.2 ⟨subd22_0_32, List.forall_mem_cons.2 ⟨subd22_0_33, List.forall_mem_cons.2 ⟨subd22_0_34, List.forall_mem_cons.2 ⟨subd22_0_35, List.forall_mem_cons.2 ⟨subd22_0_36, List.forall_mem_cons.2 ⟨subd22_0_37, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem ld_okd22_1 : ldCheck G d22_1.U d22_1.ms ldd22_1 = true := by decide +kernel
theorem pre_okd22_1 : subPre G cell22 d22_1 = true := by decide +kernel
theorem subd22_1_0 : subd22_1 [-1, -2] = true := by decide +kernel
theorem subd22_1_1 : subd22_1 [-1, -1, -8] = true := by decide +kernel
theorem subd22_1_2 : subd22_1 [-1, -1, -7] = true := by decide +kernel
theorem subd22_1_3 : subd22_1 [-1, -1, -6] = true := by decide +kernel
theorem subd22_1_4 : subd22_1 [-1, -1, -5] = true := by decide +kernel
theorem subd22_1_5 : subd22_1 [-1, -1, -4] = true := by decide +kernel
theorem subd22_1_6 : subd22_1 [-1, -1, -3] = true := by decide +kernel
theorem subd22_1_7 : subd22_1 [-1, -1, -2] = true := by decide +kernel
theorem subd22_1_8 : subd22_1 [-1, -1, -1] = true := by decide +kernel
theorem subd22_1_9 : subd22_1 [-1, -1, 0] = true := by decide +kernel
theorem subd22_1_10 : subd22_1 [-1, -1, 1] = true := by decide +kernel
theorem subd22_1_11 : subd22_1 [-1, -1, 2] = true := by decide +kernel
theorem subd22_1_12 : subd22_1 [-1, -1, 3] = true := by decide +kernel
theorem subd22_1_13 : subd22_1 [-1, -1, 4] = true := by decide +kernel
theorem subd22_1_14 : subd22_1 [-1, -1, 5] = true := by decide +kernel
theorem subd22_1_15 : subd22_1 [-1, -1, 6] = true := by decide +kernel
theorem subd22_1_16 : subd22_1 [-1, 0, -9] = true := by decide +kernel
theorem subd22_1_17 : subd22_1 [-1, 0, -8] = true := by decide +kernel
theorem subd22_1_18 : subd22_1 [-1, 0, -7] = true := by decide +kernel
theorem subd22_1_19 : subd22_1 [-1, 0, -6] = true := by decide +kernel
theorem subd22_1_20 : subd22_1 [-1, 0, -5] = true := by decide +kernel
theorem subd22_1_21 : subd22_1 [-1, 0, -4] = true := by decide +kernel
theorem subd22_1_22 : subd22_1 [-1, 0, -3] = true := by decide +kernel
theorem subd22_1_23 : subd22_1 [-1, 0, -2] = true := by decide +kernel
theorem subd22_1_24 : subd22_1 [-1, 0, -1] = true := by decide +kernel
theorem subd22_1_25 : subd22_1 [-1, 0, 0] = true := by decide +kernel
theorem subd22_1_26 : subd22_1 [-1, 0, 1] = true := by decide +kernel
theorem subd22_1_27 : subd22_1 [-1, 0, 2] = true := by decide +kernel
theorem subd22_1_28 : subd22_1 [-1, 0, 3] = true := by decide +kernel
theorem subd22_1_29 : subd22_1 [-1, 0, 4] = true := by decide +kernel
theorem subd22_1_30 : subd22_1 [-1, 0, 5] = true := by decide +kernel
theorem subd22_1_31 : subd22_1 [-1, 0, 6] = true := by decide +kernel
theorem sbd22_1_0 : ∀ q ∈ blkd22_1_0, subd22_1 q = true := by
  unfold blkd22_1_0
  exact List.forall_mem_cons.2 ⟨subd22_1_0, List.forall_mem_cons.2 ⟨subd22_1_1, List.forall_mem_cons.2 ⟨subd22_1_2, List.forall_mem_cons.2 ⟨subd22_1_3, List.forall_mem_cons.2 ⟨subd22_1_4, List.forall_mem_cons.2 ⟨subd22_1_5, List.forall_mem_cons.2 ⟨subd22_1_6, List.forall_mem_cons.2 ⟨subd22_1_7, List.forall_mem_cons.2 ⟨subd22_1_8, List.forall_mem_cons.2 ⟨subd22_1_9, List.forall_mem_cons.2 ⟨subd22_1_10, List.forall_mem_cons.2 ⟨subd22_1_11, List.forall_mem_cons.2 ⟨subd22_1_12, List.forall_mem_cons.2 ⟨subd22_1_13, List.forall_mem_cons.2 ⟨subd22_1_14, List.forall_mem_cons.2 ⟨subd22_1_15, List.forall_mem_cons.2 ⟨subd22_1_16, List.forall_mem_cons.2 ⟨subd22_1_17, List.forall_mem_cons.2 ⟨subd22_1_18, List.forall_mem_cons.2 ⟨subd22_1_19, List.forall_mem_cons.2 ⟨subd22_1_20, List.forall_mem_cons.2 ⟨subd22_1_21, List.forall_mem_cons.2 ⟨subd22_1_22, List.forall_mem_cons.2 ⟨subd22_1_23, List.forall_mem_cons.2 ⟨subd22_1_24, List.forall_mem_cons.2 ⟨subd22_1_25, List.forall_mem_cons.2 ⟨subd22_1_26, List.forall_mem_cons.2 ⟨subd22_1_27, List.forall_mem_cons.2 ⟨subd22_1_28, List.forall_mem_cons.2 ⟨subd22_1_29, List.forall_mem_cons.2 ⟨subd22_1_30, List.forall_mem_cons.2 ⟨subd22_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd22_1_32 : subd22_1 [-1, 0, 7] = true := by decide +kernel
theorem subd22_1_33 : subd22_1 [-1, 0, 8] = true := by decide +kernel
theorem subd22_1_34 : subd22_1 [-1, 1, -7] = true := by decide +kernel
theorem subd22_1_35 : subd22_1 [-1, 1, -6] = true := by decide +kernel
theorem subd22_1_36 : subd22_1 [-1, 1, -5] = true := by decide +kernel
theorem subd22_1_37 : subd22_1 [-1, 1, -4] = true := by decide +kernel
theorem subd22_1_38 : subd22_1 [-1, 1, -3] = true := by decide +kernel
theorem subd22_1_39 : subd22_1 [-1, 1, -2] = true := by decide +kernel
theorem subd22_1_40 : subd22_1 [-1, 1, -1] = true := by decide +kernel
theorem subd22_1_41 : subd22_1 [-1, 1, 0] = true := by decide +kernel
theorem subd22_1_42 : subd22_1 [-1, 1, 1] = true := by decide +kernel
theorem subd22_1_43 : subd22_1 [-1, 1, 2] = true := by decide +kernel
theorem subd22_1_44 : subd22_1 [-1, 1, 3] = true := by decide +kernel
theorem subd22_1_45 : subd22_1 [-1, 1, 4] = true := by decide +kernel
theorem subd22_1_46 : subd22_1 [-1, 1, 5] = true := by decide +kernel
theorem subd22_1_47 : subd22_1 [-1, 1, 6] = true := by decide +kernel
theorem subd22_1_48 : subd22_1 [0, -3] = true := by decide +kernel
theorem subd22_1_49 : subd22_1 [0, -2] = true := by decide +kernel
theorem subd22_1_50 : subd22_1 [0, -1, -9] = true := by decide +kernel
theorem subd22_1_51 : subd22_1 [0, -1, -8] = true := by decide +kernel
theorem subd22_1_52 : subd22_1 [0, -1, -7] = true := by decide +kernel
theorem subd22_1_53 : subd22_1 [0, -1, -6] = true := by decide +kernel
theorem subd22_1_54 : subd22_1 [0, -1, -5] = true := by decide +kernel
theorem subd22_1_55 : subd22_1 [0, -1, -4] = true := by decide +kernel
theorem subd22_1_56 : subd22_1 [0, -1, -3] = true := by decide +kernel
theorem subd22_1_57 : subd22_1 [0, -1, -2] = true := by decide +kernel
theorem subd22_1_58 : subd22_1 [0, -1, -1] = true := by decide +kernel
theorem subd22_1_59 : subd22_1 [0, -1, 0] = true := by decide +kernel
theorem subd22_1_60 : subd22_1 [0, -1, 1] = true := by decide +kernel
theorem subd22_1_61 : subd22_1 [0, -1, 2] = true := by decide +kernel
theorem subd22_1_62 : subd22_1 [0, -1, 3] = true := by decide +kernel
theorem subd22_1_63 : subd22_1 [0, -1, 4] = true := by decide +kernel
theorem sbd22_1_1 : ∀ q ∈ blkd22_1_1, subd22_1 q = true := by
  unfold blkd22_1_1
  exact List.forall_mem_cons.2 ⟨subd22_1_32, List.forall_mem_cons.2 ⟨subd22_1_33, List.forall_mem_cons.2 ⟨subd22_1_34, List.forall_mem_cons.2 ⟨subd22_1_35, List.forall_mem_cons.2 ⟨subd22_1_36, List.forall_mem_cons.2 ⟨subd22_1_37, List.forall_mem_cons.2 ⟨subd22_1_38, List.forall_mem_cons.2 ⟨subd22_1_39, List.forall_mem_cons.2 ⟨subd22_1_40, List.forall_mem_cons.2 ⟨subd22_1_41, List.forall_mem_cons.2 ⟨subd22_1_42, List.forall_mem_cons.2 ⟨subd22_1_43, List.forall_mem_cons.2 ⟨subd22_1_44, List.forall_mem_cons.2 ⟨subd22_1_45, List.forall_mem_cons.2 ⟨subd22_1_46, List.forall_mem_cons.2 ⟨subd22_1_47, List.forall_mem_cons.2 ⟨subd22_1_48, List.forall_mem_cons.2 ⟨subd22_1_49, List.forall_mem_cons.2 ⟨subd22_1_50, List.forall_mem_cons.2 ⟨subd22_1_51, List.forall_mem_cons.2 ⟨subd22_1_52, List.forall_mem_cons.2 ⟨subd22_1_53, List.forall_mem_cons.2 ⟨subd22_1_54, List.forall_mem_cons.2 ⟨subd22_1_55, List.forall_mem_cons.2 ⟨subd22_1_56, List.forall_mem_cons.2 ⟨subd22_1_57, List.forall_mem_cons.2 ⟨subd22_1_58, List.forall_mem_cons.2 ⟨subd22_1_59, List.forall_mem_cons.2 ⟨subd22_1_60, List.forall_mem_cons.2 ⟨subd22_1_61, List.forall_mem_cons.2 ⟨subd22_1_62, List.forall_mem_cons.2 ⟨subd22_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
