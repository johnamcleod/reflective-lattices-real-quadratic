import ReflectZphi.Data.Cert5.C122.Base

namespace ReflectZphi.Data.Cert5.C122

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_2_0 : subd6_2 [-3] = true := by decide +kernel
theorem subd6_2_1 : subd6_2 [-2] = true := by decide +kernel
theorem subd6_2_2 : subd6_2 [-1, -4] = true := by decide +kernel
theorem subd6_2_3 : subd6_2 [-1, -3] = true := by decide +kernel
theorem subd6_2_4 : subd6_2 [-1, -2] = true := by decide +kernel
theorem subd6_2_5 : subd6_2 [-1, -1] = true := by decide +kernel
theorem subd6_2_6 : subd6_2 [-1, 0] = true := by decide +kernel
theorem subd6_2_7 : subd6_2 [-1, 1] = true := by decide +kernel
theorem subd6_2_8 : subd6_2 [-1, 2] = true := by decide +kernel
theorem subd6_2_9 : subd6_2 [-1, 3] = true := by decide +kernel
theorem subd6_2_10 : subd6_2 [0, -4] = true := by decide +kernel
theorem subd6_2_11 : subd6_2 [0, -3] = true := by decide +kernel
theorem subd6_2_12 : subd6_2 [0, -2] = true := by decide +kernel
theorem subd6_2_13 : subd6_2 [0, -1] = true := by decide +kernel
theorem subd6_2_14 : subd6_2 [0, 0] = true := by decide +kernel
theorem subd6_2_15 : subd6_2 [0, 1] = true := by decide +kernel
theorem subd6_2_16 : subd6_2 [0, 2] = true := by decide +kernel
theorem subd6_2_17 : subd6_2 [0, 3] = true := by decide +kernel
theorem subd6_2_18 : subd6_2 [1, -4] = true := by decide +kernel
theorem subd6_2_19 : subd6_2 [1, -3] = true := by decide +kernel
theorem subd6_2_20 : subd6_2 [1, -2] = true := by decide +kernel
theorem subd6_2_21 : subd6_2 [1, -1] = true := by decide +kernel
theorem subd6_2_22 : subd6_2 [1, 0] = true := by decide +kernel
theorem subd6_2_23 : subd6_2 [1, 1] = true := by decide +kernel
theorem subd6_2_24 : subd6_2 [1, 2] = true := by decide +kernel
theorem subd6_2_25 : subd6_2 [1, 3] = true := by decide +kernel
theorem subd6_2_26 : subd6_2 [2] = true := by decide +kernel
theorem subd6_2_27 : subd6_2 [3] = true := by decide +kernel
theorem sbd6_2_0 : ∀ q ∈ blkd6_2_0, subd6_2 q = true := by
  unfold blkd6_2_0
  exact List.forall_mem_cons.2 ⟨subd6_2_0, List.forall_mem_cons.2 ⟨subd6_2_1, List.forall_mem_cons.2 ⟨subd6_2_2, List.forall_mem_cons.2 ⟨subd6_2_3, List.forall_mem_cons.2 ⟨subd6_2_4, List.forall_mem_cons.2 ⟨subd6_2_5, List.forall_mem_cons.2 ⟨subd6_2_6, List.forall_mem_cons.2 ⟨subd6_2_7, List.forall_mem_cons.2 ⟨subd6_2_8, List.forall_mem_cons.2 ⟨subd6_2_9, List.forall_mem_cons.2 ⟨subd6_2_10, List.forall_mem_cons.2 ⟨subd6_2_11, List.forall_mem_cons.2 ⟨subd6_2_12, List.forall_mem_cons.2 ⟨subd6_2_13, List.forall_mem_cons.2 ⟨subd6_2_14, List.forall_mem_cons.2 ⟨subd6_2_15, List.forall_mem_cons.2 ⟨subd6_2_16, List.forall_mem_cons.2 ⟨subd6_2_17, List.forall_mem_cons.2 ⟨subd6_2_18, List.forall_mem_cons.2 ⟨subd6_2_19, List.forall_mem_cons.2 ⟨subd6_2_20, List.forall_mem_cons.2 ⟨subd6_2_21, List.forall_mem_cons.2 ⟨subd6_2_22, List.forall_mem_cons.2 ⟨subd6_2_23, List.forall_mem_cons.2 ⟨subd6_2_24, List.forall_mem_cons.2 ⟨subd6_2_25, List.forall_mem_cons.2 ⟨subd6_2_26, List.forall_mem_cons.2 ⟨subd6_2_27, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_3 : ldCheck G d6_3.U d6_3.ms ldd6_3 = true := by decide +kernel
theorem pre_okd6_3 : subPre G cell6 d6_3 = true := by decide +kernel
theorem subd6_3_0 : subd6_3 [-3] = true := by decide +kernel
theorem subd6_3_1 : subd6_3 [-2, -5] = true := by decide +kernel
theorem subd6_3_2 : subd6_3 [-2, -4] = true := by decide +kernel
theorem subd6_3_3 : subd6_3 [-2, -3] = true := by decide +kernel
theorem subd6_3_4 : subd6_3 [-2, -2] = true := by decide +kernel
theorem subd6_3_5 : subd6_3 [-2, -1] = true := by decide +kernel
theorem subd6_3_6 : subd6_3 [-2, 0] = true := by decide +kernel
theorem subd6_3_7 : subd6_3 [-2, 1] = true := by decide +kernel
theorem subd6_3_8 : subd6_3 [-2, 2] = true := by decide +kernel
theorem subd6_3_9 : subd6_3 [-1, -5] = true := by decide +kernel
theorem subd6_3_10 : subd6_3 [-1, -4] = true := by decide +kernel
theorem subd6_3_11 : subd6_3 [-1, -3] = true := by decide +kernel
theorem subd6_3_12 : subd6_3 [-1, -2] = true := by decide +kernel
theorem subd6_3_13 : subd6_3 [-1, -1] = true := by decide +kernel
theorem subd6_3_14 : subd6_3 [-1, 0] = true := by decide +kernel
theorem subd6_3_15 : subd6_3 [-1, 1] = true := by decide +kernel
theorem subd6_3_16 : subd6_3 [-1, 2] = true := by decide +kernel
theorem subd6_3_17 : subd6_3 [-1, 3] = true := by decide +kernel
theorem subd6_3_18 : subd6_3 [0, -5] = true := by decide +kernel
theorem subd6_3_19 : subd6_3 [0, -4] = true := by decide +kernel
theorem subd6_3_20 : subd6_3 [0, -3] = true := by decide +kernel
theorem subd6_3_21 : subd6_3 [0, -2] = true := by decide +kernel
theorem subd6_3_22 : subd6_3 [0, -1] = true := by decide +kernel
theorem subd6_3_23 : subd6_3 [0, 0] = true := by decide +kernel
theorem subd6_3_24 : subd6_3 [0, 1] = true := by decide +kernel
theorem subd6_3_25 : subd6_3 [0, 2] = true := by decide +kernel
theorem subd6_3_26 : subd6_3 [0, 3] = true := by decide +kernel
theorem subd6_3_27 : subd6_3 [0, 4] = true := by decide +kernel
theorem subd6_3_28 : subd6_3 [1, -4] = true := by decide +kernel
theorem subd6_3_29 : subd6_3 [1, -3] = true := by decide +kernel
theorem subd6_3_30 : subd6_3 [1, -2] = true := by decide +kernel
theorem subd6_3_31 : subd6_3 [1, -1] = true := by decide +kernel
theorem sbd6_3_0 : ∀ q ∈ blkd6_3_0, subd6_3 q = true := by
  unfold blkd6_3_0
  exact List.forall_mem_cons.2 ⟨subd6_3_0, List.forall_mem_cons.2 ⟨subd6_3_1, List.forall_mem_cons.2 ⟨subd6_3_2, List.forall_mem_cons.2 ⟨subd6_3_3, List.forall_mem_cons.2 ⟨subd6_3_4, List.forall_mem_cons.2 ⟨subd6_3_5, List.forall_mem_cons.2 ⟨subd6_3_6, List.forall_mem_cons.2 ⟨subd6_3_7, List.forall_mem_cons.2 ⟨subd6_3_8, List.forall_mem_cons.2 ⟨subd6_3_9, List.forall_mem_cons.2 ⟨subd6_3_10, List.forall_mem_cons.2 ⟨subd6_3_11, List.forall_mem_cons.2 ⟨subd6_3_12, List.forall_mem_cons.2 ⟨subd6_3_13, List.forall_mem_cons.2 ⟨subd6_3_14, List.forall_mem_cons.2 ⟨subd6_3_15, List.forall_mem_cons.2 ⟨subd6_3_16, List.forall_mem_cons.2 ⟨subd6_3_17, List.forall_mem_cons.2 ⟨subd6_3_18, List.forall_mem_cons.2 ⟨subd6_3_19, List.forall_mem_cons.2 ⟨subd6_3_20, List.forall_mem_cons.2 ⟨subd6_3_21, List.forall_mem_cons.2 ⟨subd6_3_22, List.forall_mem_cons.2 ⟨subd6_3_23, List.forall_mem_cons.2 ⟨subd6_3_24, List.forall_mem_cons.2 ⟨subd6_3_25, List.forall_mem_cons.2 ⟨subd6_3_26, List.forall_mem_cons.2 ⟨subd6_3_27, List.forall_mem_cons.2 ⟨subd6_3_28, List.forall_mem_cons.2 ⟨subd6_3_29, List.forall_mem_cons.2 ⟨subd6_3_30, List.forall_mem_cons.2 ⟨subd6_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_3_32 : subd6_3 [1, 0] = true := by decide +kernel
theorem subd6_3_33 : subd6_3 [1, 1] = true := by decide +kernel
theorem subd6_3_34 : subd6_3 [1, 2] = true := by decide +kernel
theorem subd6_3_35 : subd6_3 [1, 3] = true := by decide +kernel
theorem subd6_3_36 : subd6_3 [1, 4] = true := by decide +kernel
theorem subd6_3_37 : subd6_3 [2, -3] = true := by decide +kernel
theorem subd6_3_38 : subd6_3 [2, -2] = true := by decide +kernel
theorem subd6_3_39 : subd6_3 [2, -1] = true := by decide +kernel
theorem subd6_3_40 : subd6_3 [2, 0] = true := by decide +kernel
theorem subd6_3_41 : subd6_3 [2, 1] = true := by decide +kernel
theorem subd6_3_42 : subd6_3 [2, 2] = true := by decide +kernel
theorem subd6_3_43 : subd6_3 [2, 3] = true := by decide +kernel
theorem subd6_3_44 : subd6_3 [2, 4] = true := by decide +kernel
theorem subd6_3_45 : subd6_3 [3] = true := by decide +kernel
theorem sbd6_3_1 : ∀ q ∈ blkd6_3_1, subd6_3 q = true := by
  unfold blkd6_3_1
  exact List.forall_mem_cons.2 ⟨subd6_3_32, List.forall_mem_cons.2 ⟨subd6_3_33, List.forall_mem_cons.2 ⟨subd6_3_34, List.forall_mem_cons.2 ⟨subd6_3_35, List.forall_mem_cons.2 ⟨subd6_3_36, List.forall_mem_cons.2 ⟨subd6_3_37, List.forall_mem_cons.2 ⟨subd6_3_38, List.forall_mem_cons.2 ⟨subd6_3_39, List.forall_mem_cons.2 ⟨subd6_3_40, List.forall_mem_cons.2 ⟨subd6_3_41, List.forall_mem_cons.2 ⟨subd6_3_42, List.forall_mem_cons.2 ⟨subd6_3_43, List.forall_mem_cons.2 ⟨subd6_3_44, List.forall_mem_cons.2 ⟨subd6_3_45, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_4 : ldCheck G d6_4.U d6_4.ms ldd6_4 = true := by decide +kernel
theorem pre_okd6_4 : subPre G cell6 d6_4 = true := by decide +kernel
theorem subd6_4_0 : subd6_4 [-2, -2] = true := by decide +kernel
theorem subd6_4_1 : subd6_4 [-2, -1] = true := by decide +kernel
theorem subd6_4_2 : subd6_4 [-2, 0] = true := by decide +kernel
theorem subd6_4_3 : subd6_4 [-2, 1] = true := by decide +kernel
theorem subd6_4_4 : subd6_4 [-1, -3] = true := by decide +kernel
theorem subd6_4_5 : subd6_4 [-1, -2] = true := by decide +kernel
theorem subd6_4_6 : subd6_4 [-1, -1, -8] = true := by decide +kernel
theorem subd6_4_7 : subd6_4 [-1, -1, -7] = true := by decide +kernel
theorem subd6_4_8 : subd6_4 [-1, -1, -6] = true := by decide +kernel
theorem subd6_4_9 : subd6_4 [-1, -1, -5] = true := by decide +kernel
theorem subd6_4_10 : subd6_4 [-1, -1, -4] = true := by decide +kernel
theorem subd6_4_11 : subd6_4 [-1, -1, -3] = true := by decide +kernel
theorem subd6_4_12 : subd6_4 [-1, -1, -2] = true := by decide +kernel
theorem subd6_4_13 : subd6_4 [-1, -1, -1] = true := by decide +kernel
theorem subd6_4_14 : subd6_4 [-1, -1, 0] = true := by decide +kernel
theorem subd6_4_15 : subd6_4 [-1, -1, 1] = true := by decide +kernel
theorem subd6_4_16 : subd6_4 [-1, -1, 2] = true := by decide +kernel
theorem subd6_4_17 : subd6_4 [-1, -1, 3] = true := by decide +kernel
theorem subd6_4_18 : subd6_4 [-1, -1, 4] = true := by decide +kernel
theorem subd6_4_19 : subd6_4 [-1, -1, 5] = true := by decide +kernel
theorem subd6_4_20 : subd6_4 [-1, -1, 6] = true := by decide +kernel
theorem subd6_4_21 : subd6_4 [-1, -1, 7] = true := by decide +kernel
theorem subd6_4_22 : subd6_4 [-1, -1, 8] = true := by decide +kernel
theorem subd6_4_23 : subd6_4 [-1, 0, -9] = true := by decide +kernel
theorem subd6_4_24 : subd6_4 [-1, 0, -8] = true := by decide +kernel
theorem subd6_4_25 : subd6_4 [-1, 0, -7] = true := by decide +kernel
theorem subd6_4_26 : subd6_4 [-1, 0, -6] = true := by decide +kernel
theorem subd6_4_27 : subd6_4 [-1, 0, -5] = true := by decide +kernel
theorem subd6_4_28 : subd6_4 [-1, 0, -4] = true := by decide +kernel
theorem subd6_4_29 : subd6_4 [-1, 0, -3] = true := by decide +kernel
theorem subd6_4_30 : subd6_4 [-1, 0, -2] = true := by decide +kernel
theorem subd6_4_31 : subd6_4 [-1, 0, -1] = true := by decide +kernel
theorem sbd6_4_0 : ∀ q ∈ blkd6_4_0, subd6_4 q = true := by
  unfold blkd6_4_0
  exact List.forall_mem_cons.2 ⟨subd6_4_0, List.forall_mem_cons.2 ⟨subd6_4_1, List.forall_mem_cons.2 ⟨subd6_4_2, List.forall_mem_cons.2 ⟨subd6_4_3, List.forall_mem_cons.2 ⟨subd6_4_4, List.forall_mem_cons.2 ⟨subd6_4_5, List.forall_mem_cons.2 ⟨subd6_4_6, List.forall_mem_cons.2 ⟨subd6_4_7, List.forall_mem_cons.2 ⟨subd6_4_8, List.forall_mem_cons.2 ⟨subd6_4_9, List.forall_mem_cons.2 ⟨subd6_4_10, List.forall_mem_cons.2 ⟨subd6_4_11, List.forall_mem_cons.2 ⟨subd6_4_12, List.forall_mem_cons.2 ⟨subd6_4_13, List.forall_mem_cons.2 ⟨subd6_4_14, List.forall_mem_cons.2 ⟨subd6_4_15, List.forall_mem_cons.2 ⟨subd6_4_16, List.forall_mem_cons.2 ⟨subd6_4_17, List.forall_mem_cons.2 ⟨subd6_4_18, List.forall_mem_cons.2 ⟨subd6_4_19, List.forall_mem_cons.2 ⟨subd6_4_20, List.forall_mem_cons.2 ⟨subd6_4_21, List.forall_mem_cons.2 ⟨subd6_4_22, List.forall_mem_cons.2 ⟨subd6_4_23, List.forall_mem_cons.2 ⟨subd6_4_24, List.forall_mem_cons.2 ⟨subd6_4_25, List.forall_mem_cons.2 ⟨subd6_4_26, List.forall_mem_cons.2 ⟨subd6_4_27, List.forall_mem_cons.2 ⟨subd6_4_28, List.forall_mem_cons.2 ⟨subd6_4_29, List.forall_mem_cons.2 ⟨subd6_4_30, List.forall_mem_cons.2 ⟨subd6_4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_4_32 : subd6_4 [-1, 0, 0] = true := by decide +kernel
theorem subd6_4_33 : subd6_4 [-1, 0, 1] = true := by decide +kernel
theorem subd6_4_34 : subd6_4 [-1, 0, 2] = true := by decide +kernel
theorem subd6_4_35 : subd6_4 [-1, 0, 3] = true := by decide +kernel
theorem subd6_4_36 : subd6_4 [-1, 0, 4] = true := by decide +kernel
theorem subd6_4_37 : subd6_4 [-1, 0, 5] = true := by decide +kernel
theorem subd6_4_38 : subd6_4 [-1, 0, 6] = true := by decide +kernel
theorem subd6_4_39 : subd6_4 [-1, 0, 7] = true := by decide +kernel
theorem subd6_4_40 : subd6_4 [-1, 0, 8] = true := by decide +kernel
theorem subd6_4_41 : subd6_4 [-1, 1, -8] = true := by decide +kernel
theorem subd6_4_42 : subd6_4 [-1, 1, -7] = true := by decide +kernel
theorem subd6_4_43 : subd6_4 [-1, 1, -6] = true := by decide +kernel
theorem subd6_4_44 : subd6_4 [-1, 1, -5] = true := by decide +kernel
theorem subd6_4_45 : subd6_4 [-1, 1, -4] = true := by decide +kernel
theorem subd6_4_46 : subd6_4 [-1, 1, -3] = true := by decide +kernel
theorem subd6_4_47 : subd6_4 [-1, 1, -2] = true := by decide +kernel
theorem subd6_4_48 : subd6_4 [-1, 1, -1] = true := by decide +kernel
theorem subd6_4_49 : subd6_4 [-1, 1, 0] = true := by decide +kernel
theorem subd6_4_50 : subd6_4 [-1, 1, 1] = true := by decide +kernel
theorem subd6_4_51 : subd6_4 [-1, 1, 2] = true := by decide +kernel
theorem subd6_4_52 : subd6_4 [-1, 1, 3] = true := by decide +kernel
theorem subd6_4_53 : subd6_4 [-1, 1, 4] = true := by decide +kernel
theorem subd6_4_54 : subd6_4 [-1, 1, 5] = true := by decide +kernel
theorem subd6_4_55 : subd6_4 [-1, 1, 6] = true := by decide +kernel
theorem subd6_4_56 : subd6_4 [-1, 1, 7] = true := by decide +kernel
theorem subd6_4_57 : subd6_4 [-1, 2] = true := by decide +kernel
theorem subd6_4_58 : subd6_4 [0, -3] = true := by decide +kernel
theorem subd6_4_59 : subd6_4 [0, -2] = true := by decide +kernel
theorem subd6_4_60 : subd6_4 [0, -1, -9] = true := by decide +kernel
theorem subd6_4_61 : subd6_4 [0, -1, -8] = true := by decide +kernel
theorem subd6_4_62 : subd6_4 [0, -1, -7] = true := by decide +kernel
theorem subd6_4_63 : subd6_4 [0, -1, -6] = true := by decide +kernel
theorem sbd6_4_1 : ∀ q ∈ blkd6_4_1, subd6_4 q = true := by
  unfold blkd6_4_1
  exact List.forall_mem_cons.2 ⟨subd6_4_32, List.forall_mem_cons.2 ⟨subd6_4_33, List.forall_mem_cons.2 ⟨subd6_4_34, List.forall_mem_cons.2 ⟨subd6_4_35, List.forall_mem_cons.2 ⟨subd6_4_36, List.forall_mem_cons.2 ⟨subd6_4_37, List.forall_mem_cons.2 ⟨subd6_4_38, List.forall_mem_cons.2 ⟨subd6_4_39, List.forall_mem_cons.2 ⟨subd6_4_40, List.forall_mem_cons.2 ⟨subd6_4_41, List.forall_mem_cons.2 ⟨subd6_4_42, List.forall_mem_cons.2 ⟨subd6_4_43, List.forall_mem_cons.2 ⟨subd6_4_44, List.forall_mem_cons.2 ⟨subd6_4_45, List.forall_mem_cons.2 ⟨subd6_4_46, List.forall_mem_cons.2 ⟨subd6_4_47, List.forall_mem_cons.2 ⟨subd6_4_48, List.forall_mem_cons.2 ⟨subd6_4_49, List.forall_mem_cons.2 ⟨subd6_4_50, List.forall_mem_cons.2 ⟨subd6_4_51, List.forall_mem_cons.2 ⟨subd6_4_52, List.forall_mem_cons.2 ⟨subd6_4_53, List.forall_mem_cons.2 ⟨subd6_4_54, List.forall_mem_cons.2 ⟨subd6_4_55, List.forall_mem_cons.2 ⟨subd6_4_56, List.forall_mem_cons.2 ⟨subd6_4_57, List.forall_mem_cons.2 ⟨subd6_4_58, List.forall_mem_cons.2 ⟨subd6_4_59, List.forall_mem_cons.2 ⟨subd6_4_60, List.forall_mem_cons.2 ⟨subd6_4_61, List.forall_mem_cons.2 ⟨subd6_4_62, List.forall_mem_cons.2 ⟨subd6_4_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_4_64 : subd6_4 [0, -1, -5] = true := by decide +kernel
theorem subd6_4_65 : subd6_4 [0, -1, -4] = true := by decide +kernel
theorem subd6_4_66 : subd6_4 [0, -1, -3] = true := by decide +kernel
theorem subd6_4_67 : subd6_4 [0, -1, -2] = true := by decide +kernel
theorem subd6_4_68 : subd6_4 [0, -1, -1] = true := by decide +kernel
theorem subd6_4_69 : subd6_4 [0, -1, 0] = true := by decide +kernel
theorem subd6_4_70 : subd6_4 [0, -1, 1] = true := by decide +kernel
theorem subd6_4_71 : subd6_4 [0, -1, 2] = true := by decide +kernel
theorem subd6_4_72 : subd6_4 [0, -1, 3] = true := by decide +kernel
theorem subd6_4_73 : subd6_4 [0, -1, 4] = true := by decide +kernel
theorem subd6_4_74 : subd6_4 [0, -1, 5] = true := by decide +kernel
theorem subd6_4_75 : subd6_4 [0, -1, 6] = true := by decide +kernel
theorem subd6_4_76 : subd6_4 [0, -1, 7] = true := by decide +kernel
theorem subd6_4_77 : subd6_4 [0, -1, 8] = true := by decide +kernel
theorem subd6_4_78 : subd6_4 [0, 0, -10] = true := by decide +kernel
theorem subd6_4_79 : subd6_4 [0, 0, -9] = true := by decide +kernel
theorem subd6_4_80 : subd6_4 [0, 0, -8] = true := by decide +kernel
theorem subd6_4_81 : subd6_4 [0, 0, -7] = true := by decide +kernel
theorem subd6_4_82 : subd6_4 [0, 0, -6] = true := by decide +kernel
theorem subd6_4_83 : subd6_4 [0, 0, -5] = true := by decide +kernel
theorem subd6_4_84 : subd6_4 [0, 0, -4] = true := by decide +kernel
theorem subd6_4_85 : subd6_4 [0, 0, -3] = true := by decide +kernel
theorem subd6_4_86 : subd6_4 [0, 0, -2] = true := by decide +kernel
theorem subd6_4_87 : subd6_4 [0, 0, -1] = true := by decide +kernel
theorem subd6_4_88 : subd6_4 [0, 0, 0] = true := by decide +kernel
theorem subd6_4_89 : subd6_4 [0, 0, 1] = true := by decide +kernel
theorem subd6_4_90 : subd6_4 [0, 0, 2] = true := by decide +kernel
theorem subd6_4_91 : subd6_4 [0, 0, 3] = true := by decide +kernel
theorem subd6_4_92 : subd6_4 [0, 0, 4] = true := by decide +kernel
theorem subd6_4_93 : subd6_4 [0, 0, 5] = true := by decide +kernel
theorem subd6_4_94 : subd6_4 [0, 0, 6] = true := by decide +kernel
theorem subd6_4_95 : subd6_4 [0, 0, 7] = true := by decide +kernel
theorem sbd6_4_2 : ∀ q ∈ blkd6_4_2, subd6_4 q = true := by
  unfold blkd6_4_2
  exact List.forall_mem_cons.2 ⟨subd6_4_64, List.forall_mem_cons.2 ⟨subd6_4_65, List.forall_mem_cons.2 ⟨subd6_4_66, List.forall_mem_cons.2 ⟨subd6_4_67, List.forall_mem_cons.2 ⟨subd6_4_68, List.forall_mem_cons.2 ⟨subd6_4_69, List.forall_mem_cons.2 ⟨subd6_4_70, List.forall_mem_cons.2 ⟨subd6_4_71, List.forall_mem_cons.2 ⟨subd6_4_72, List.forall_mem_cons.2 ⟨subd6_4_73, List.forall_mem_cons.2 ⟨subd6_4_74, List.forall_mem_cons.2 ⟨subd6_4_75, List.forall_mem_cons.2 ⟨subd6_4_76, List.forall_mem_cons.2 ⟨subd6_4_77, List.forall_mem_cons.2 ⟨subd6_4_78, List.forall_mem_cons.2 ⟨subd6_4_79, List.forall_mem_cons.2 ⟨subd6_4_80, List.forall_mem_cons.2 ⟨subd6_4_81, List.forall_mem_cons.2 ⟨subd6_4_82, List.forall_mem_cons.2 ⟨subd6_4_83, List.forall_mem_cons.2 ⟨subd6_4_84, List.forall_mem_cons.2 ⟨subd6_4_85, List.forall_mem_cons.2 ⟨subd6_4_86, List.forall_mem_cons.2 ⟨subd6_4_87, List.forall_mem_cons.2 ⟨subd6_4_88, List.forall_mem_cons.2 ⟨subd6_4_89, List.forall_mem_cons.2 ⟨subd6_4_90, List.forall_mem_cons.2 ⟨subd6_4_91, List.forall_mem_cons.2 ⟨subd6_4_92, List.forall_mem_cons.2 ⟨subd6_4_93, List.forall_mem_cons.2 ⟨subd6_4_94, List.forall_mem_cons.2 ⟨subd6_4_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_4_96 : subd6_4 [0, 0, 8] = true := by decide +kernel
theorem subd6_4_97 : subd6_4 [0, 0, 9] = true := by decide +kernel
theorem subd6_4_98 : subd6_4 [0, 1, -9] = true := by decide +kernel
theorem subd6_4_99 : subd6_4 [0, 1, -8] = true := by decide +kernel
theorem subd6_4_100 : subd6_4 [0, 1, -7] = true := by decide +kernel
theorem subd6_4_101 : subd6_4 [0, 1, -6] = true := by decide +kernel
theorem subd6_4_102 : subd6_4 [0, 1, -5] = true := by decide +kernel
theorem subd6_4_103 : subd6_4 [0, 1, -4] = true := by decide +kernel
theorem subd6_4_104 : subd6_4 [0, 1, -3] = true := by decide +kernel
theorem subd6_4_105 : subd6_4 [0, 1, -2] = true := by decide +kernel
theorem subd6_4_106 : subd6_4 [0, 1, -1] = true := by decide +kernel
theorem subd6_4_107 : subd6_4 [0, 1, 0] = true := by decide +kernel
theorem subd6_4_108 : subd6_4 [0, 1, 1] = true := by decide +kernel
theorem subd6_4_109 : subd6_4 [0, 1, 2] = true := by decide +kernel
theorem subd6_4_110 : subd6_4 [0, 1, 3] = true := by decide +kernel
theorem subd6_4_111 : subd6_4 [0, 1, 4] = true := by decide +kernel
theorem subd6_4_112 : subd6_4 [0, 1, 5] = true := by decide +kernel
theorem subd6_4_113 : subd6_4 [0, 1, 6] = true := by decide +kernel
theorem subd6_4_114 : subd6_4 [0, 1, 7] = true := by decide +kernel
theorem subd6_4_115 : subd6_4 [0, 1, 8] = true := by decide +kernel
theorem subd6_4_116 : subd6_4 [0, 2] = true := by decide +kernel
theorem subd6_4_117 : subd6_4 [1, -3] = true := by decide +kernel
theorem subd6_4_118 : subd6_4 [1, -2] = true := by decide +kernel
theorem subd6_4_119 : subd6_4 [1, -1, -8] = true := by decide +kernel
theorem subd6_4_120 : subd6_4 [1, -1, -7] = true := by decide +kernel
theorem subd6_4_121 : subd6_4 [1, -1, -6] = true := by decide +kernel
theorem subd6_4_122 : subd6_4 [1, -1, -5] = true := by decide +kernel
theorem subd6_4_123 : subd6_4 [1, -1, -4] = true := by decide +kernel
theorem subd6_4_124 : subd6_4 [1, -1, -3] = true := by decide +kernel
theorem subd6_4_125 : subd6_4 [1, -1, -2] = true := by decide +kernel
theorem subd6_4_126 : subd6_4 [1, -1, -1] = true := by decide +kernel
theorem subd6_4_127 : subd6_4 [1, -1, 0] = true := by decide +kernel
theorem sbd6_4_3 : ∀ q ∈ blkd6_4_3, subd6_4 q = true := by
  unfold blkd6_4_3
  exact List.forall_mem_cons.2 ⟨subd6_4_96, List.forall_mem_cons.2 ⟨subd6_4_97, List.forall_mem_cons.2 ⟨subd6_4_98, List.forall_mem_cons.2 ⟨subd6_4_99, List.forall_mem_cons.2 ⟨subd6_4_100, List.forall_mem_cons.2 ⟨subd6_4_101, List.forall_mem_cons.2 ⟨subd6_4_102, List.forall_mem_cons.2 ⟨subd6_4_103, List.forall_mem_cons.2 ⟨subd6_4_104, List.forall_mem_cons.2 ⟨subd6_4_105, List.forall_mem_cons.2 ⟨subd6_4_106, List.forall_mem_cons.2 ⟨subd6_4_107, List.forall_mem_cons.2 ⟨subd6_4_108, List.forall_mem_cons.2 ⟨subd6_4_109, List.forall_mem_cons.2 ⟨subd6_4_110, List.forall_mem_cons.2 ⟨subd6_4_111, List.forall_mem_cons.2 ⟨subd6_4_112, List.forall_mem_cons.2 ⟨subd6_4_113, List.forall_mem_cons.2 ⟨subd6_4_114, List.forall_mem_cons.2 ⟨subd6_4_115, List.forall_mem_cons.2 ⟨subd6_4_116, List.forall_mem_cons.2 ⟨subd6_4_117, List.forall_mem_cons.2 ⟨subd6_4_118, List.forall_mem_cons.2 ⟨subd6_4_119, List.forall_mem_cons.2 ⟨subd6_4_120, List.forall_mem_cons.2 ⟨subd6_4_121, List.forall_mem_cons.2 ⟨subd6_4_122, List.forall_mem_cons.2 ⟨subd6_4_123, List.forall_mem_cons.2 ⟨subd6_4_124, List.forall_mem_cons.2 ⟨subd6_4_125, List.forall_mem_cons.2 ⟨subd6_4_126, List.forall_mem_cons.2 ⟨subd6_4_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_4_128 : subd6_4 [1, -1, 1] = true := by decide +kernel
theorem subd6_4_129 : subd6_4 [1, -1, 2] = true := by decide +kernel
theorem subd6_4_130 : subd6_4 [1, -1, 3] = true := by decide +kernel
theorem subd6_4_131 : subd6_4 [1, -1, 4] = true := by decide +kernel
theorem subd6_4_132 : subd6_4 [1, -1, 5] = true := by decide +kernel
theorem subd6_4_133 : subd6_4 [1, -1, 6] = true := by decide +kernel
theorem subd6_4_134 : subd6_4 [1, -1, 7] = true := by decide +kernel
theorem subd6_4_135 : subd6_4 [1, 0, -9] = true := by decide +kernel
theorem subd6_4_136 : subd6_4 [1, 0, -8] = true := by decide +kernel
theorem subd6_4_137 : subd6_4 [1, 0, -7] = true := by decide +kernel
theorem subd6_4_138 : subd6_4 [1, 0, -6] = true := by decide +kernel
theorem subd6_4_139 : subd6_4 [1, 0, -5] = true := by decide +kernel
theorem subd6_4_140 : subd6_4 [1, 0, -4] = true := by decide +kernel
theorem subd6_4_141 : subd6_4 [1, 0, -3] = true := by decide +kernel
theorem subd6_4_142 : subd6_4 [1, 0, -2] = true := by decide +kernel
theorem subd6_4_143 : subd6_4 [1, 0, -1] = true := by decide +kernel
theorem subd6_4_144 : subd6_4 [1, 0, 0] = true := by decide +kernel
theorem subd6_4_145 : subd6_4 [1, 0, 1] = true := by decide +kernel
theorem subd6_4_146 : subd6_4 [1, 0, 2] = true := by decide +kernel
theorem subd6_4_147 : subd6_4 [1, 0, 3] = true := by decide +kernel
theorem subd6_4_148 : subd6_4 [1, 0, 4] = true := by decide +kernel
theorem subd6_4_149 : subd6_4 [1, 0, 5] = true := by decide +kernel
theorem subd6_4_150 : subd6_4 [1, 0, 6] = true := by decide +kernel
theorem subd6_4_151 : subd6_4 [1, 0, 7] = true := by decide +kernel
theorem subd6_4_152 : subd6_4 [1, 0, 8] = true := by decide +kernel
theorem subd6_4_153 : subd6_4 [1, 1, -9] = true := by decide +kernel
theorem subd6_4_154 : subd6_4 [1, 1, -8] = true := by decide +kernel
theorem subd6_4_155 : subd6_4 [1, 1, -7] = true := by decide +kernel
theorem subd6_4_156 : subd6_4 [1, 1, -6] = true := by decide +kernel
theorem subd6_4_157 : subd6_4 [1, 1, -5] = true := by decide +kernel
theorem subd6_4_158 : subd6_4 [1, 1, -4] = true := by decide +kernel
theorem subd6_4_159 : subd6_4 [1, 1, -3] = true := by decide +kernel
theorem sbd6_4_4 : ∀ q ∈ blkd6_4_4, subd6_4 q = true := by
  unfold blkd6_4_4
  exact List.forall_mem_cons.2 ⟨subd6_4_128, List.forall_mem_cons.2 ⟨subd6_4_129, List.forall_mem_cons.2 ⟨subd6_4_130, List.forall_mem_cons.2 ⟨subd6_4_131, List.forall_mem_cons.2 ⟨subd6_4_132, List.forall_mem_cons.2 ⟨subd6_4_133, List.forall_mem_cons.2 ⟨subd6_4_134, List.forall_mem_cons.2 ⟨subd6_4_135, List.forall_mem_cons.2 ⟨subd6_4_136, List.forall_mem_cons.2 ⟨subd6_4_137, List.forall_mem_cons.2 ⟨subd6_4_138, List.forall_mem_cons.2 ⟨subd6_4_139, List.forall_mem_cons.2 ⟨subd6_4_140, List.forall_mem_cons.2 ⟨subd6_4_141, List.forall_mem_cons.2 ⟨subd6_4_142, List.forall_mem_cons.2 ⟨subd6_4_143, List.forall_mem_cons.2 ⟨subd6_4_144, List.forall_mem_cons.2 ⟨subd6_4_145, List.forall_mem_cons.2 ⟨subd6_4_146, List.forall_mem_cons.2 ⟨subd6_4_147, List.forall_mem_cons.2 ⟨subd6_4_148, List.forall_mem_cons.2 ⟨subd6_4_149, List.forall_mem_cons.2 ⟨subd6_4_150, List.forall_mem_cons.2 ⟨subd6_4_151, List.forall_mem_cons.2 ⟨subd6_4_152, List.forall_mem_cons.2 ⟨subd6_4_153, List.forall_mem_cons.2 ⟨subd6_4_154, List.forall_mem_cons.2 ⟨subd6_4_155, List.forall_mem_cons.2 ⟨subd6_4_156, List.forall_mem_cons.2 ⟨subd6_4_157, List.forall_mem_cons.2 ⟨subd6_4_158, List.forall_mem_cons.2 ⟨subd6_4_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C122
